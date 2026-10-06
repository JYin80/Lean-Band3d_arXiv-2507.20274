Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 01:57:00 UTC 2026

Notation: `W^d·L^d = N = sz.size n` (`Defs/Sizes.lean:157`), `β_u = c_u − L^{-d}`, `B_c = Σ_u β_u E_u`,
`E_u = W^{-d}1_{[u]}`, `Σ_u L^{-d}E_u = N^{-1}·1`, `G = green H z = (H − z)⁻¹` (`EntryCore.lean:34`), `Gn = Gres (seqXmat) z true = green` (`cont_Gres_true_eq_green`, `ContinuityNet.lean:430`).

### (i) Exponent table

| Quantity | Value / form | Constraint it must satisfy | Slack |
|---|---|---|---|
| spectral weight `w_k = Im (μ_k − z)⁻¹`, `z = E+iη` | `η/((μ_k−E)²+η²)` | `≥ 1/(2η)` iff `\|μ_k−E\| ≤ η` | equality at `\|μ_k−E\| = η` |
| `(ssfa2)` constant | `\|ψ_k^*Bψ_k'\|² ≤ 4η² Re tr(ImG B ImG B)` | `tr(ImG B ImG B) = Σ_{l,m} w_l w_m \|ψ_l^*Bψ_m\|² ≥ w_k w_k' \|ψ_k^*Bψ_k'\|²` for `B = B^*`; `4 = (2η·w)^{-2}` | sharp (single term kept, all others `≥ 0`) |
| trace algebra | `tr(ImG E_u ImG E_v) = −¼(T₊(u,v) + conj T₊(u,v) − T₋(v,u) − T₋(u,v))`, `T₊ = avg2(G_xy G_yx)`, `T₋ = avg2 \|G_xy\|²` | `tr(GE_uGE_v) = T₊(u,v)`, `tr(GE_uG^*E_v) = T₋(u,v)`, `tr(G^*E_uGE_v) = T₋(v,u)`, `tr(G^*E_uG^*E_v) = conj T₊(u,v)` | exact; numerically `\|X − formula\| = 2.2e-18` (script 1) |
| `Σ_u β_u` | `0` | `Σ c_u = 1`, `Σ_u L^{-d} = 1` (`card Zd d L = L^d`) | exact |
| `Σ_u \|β_u\|` | `≤ 2` | `≤ Σ c_u + Σ L^{-d} = 2` | factor 2 (observed 0.456 at random `c`) |
| row-difference reduction | `Σ_{u,v}β_uβ_vP(u,v) = Σ_uβ_u Σ_vβ_v(P(u,v) − P(u,u))` | uses `Σ_vβ_v = 0`; `\|·\| ≤ Σ\|β_u\|·2·K ≤ 4K` | hypothesis is in the 2nd index `b, b'` for all `a`; the `T₋(v,u)` sum is renamed `u↔v` first |
| core constant | `E X_c ≤ 4(K + ε)` | profile part `¼(2·4K + 4K + 4K) = 4K`; error part `¼(2·4ε + 4ε + 4ε) = 4ε` (uses `(Σ\|β\|)² ≤ 4`) | random-profile test: `\|profile part\|/K ≤ 0.258 ≤ 4` (script 1) |
| `X_c ≥ 0` for every `ω` | `Re tr(ImG B_c ImG B_c) ≥ 0` | `H` Hermitian (`seqXmat_isHermitian`), `B_c = B_c^*` (real `β_u`, real diagonal), `Im z > 0` so `w_l > 0` | none needed |
| integrability of `X_c` | `\|G_xy\| ≤ (Im z)⁻¹`, `X_c` a finite sum of products of 4 entries and constants | measurability of `ω ↦ G_xy` (merged lead, not in the five imports: `Green/LDE.lean:122 measurable_green_apply`, stated for `seqHflow sz n u`; `seqHflow sz n 1 = seqXmat` needs `√1 = 1`) | bounded entries make the finite sum bounded |
| `queBad_sub` threshold | `\|ψ_i^*B_{δ_a}ψ_j\| = W^{-d}\|Σ_{x∈[a]} ψ̄_iψ_j − (W^d/N)δ_{ij}\| ≥ W^{-d}·W^{d−c}/N = W^{-c}/N` | then `W^{-2c}/N² ≤ \|ψ_i^*Bψ_j\|² ≤ 4η²X` gives `W^{-2c} ≤ 4N²η²X`; no constraint on `ε₀, c` (any real) | equality of exponents: `W^{-d}W^{d−c}` (script 2: `0.8909 = 0.8909`) |
| `que2Bad_sub` threshold | `ψ_k^*B_{1_A/\|A\|}ψ_k = (W^d\|A\|)⁻¹(Σ_{u∈A}Σ_{x∈[u]}\|ψ_k\|² − W^d\|A\|/N)` (uses `Σ_x\|ψ_k(x)\|² = 1`) `≥ (W^d\|A\|)⁻¹·W^{d−c}\|A\|/N = W^{-c}/N` | `A` nonempty (`\|A\|⁻¹`) | same as above |
| window `queWindow` | half-width `h = W^{-ε₀}·lam·W^{d/2}/N` | hypothesis `h ≤ η` (the pin's `∀ x, queWindow … x → \|x−E\| ≤ η`, `η = h` is the paper's choice `1_2:523`) | instance: `h = 1.20e-6`, `η = 1`: factor `8.3e5` |
| `MAThetaDiff` | `‖Θ_ab − Θ_ab'‖ ≤ C g^{-2}` for `ξ = \|m\|²` and `ξ = m²` | `3 ≤ d`, `3 ≤ L`, `0 < g ≤ 𝔡⁻¹`, `0 < Im z ≤ 1`, `\|Re z\| ≤ 2−κ`; `C = 2C₈(d, 𝔡⁻¹, √(κ(4−κ))/2, 1/2)` from `prop5to8_holds`; the probe proof (`T2192Pins.lean:706-770`) uses `‖ξ‖ < 1` from `0<‖msc z‖<1` | instance `g = 1/64 ≤ 10`; no `log L` (that is `d = 2`) |
| MA-05b consumer `K` | `K = C g^{-2}W^{-d}` | `‖profPM(a,b) − profPM(a,b')‖ = ‖msc z‖²‖ΔΘ‖/W^d ≤ K` since `‖msc z‖ < 1`; same for `profPP` (`m²`) | factor `‖msc z‖² < 1` |
| MA-05b consumer `ε` | `ε = qdBoundExp τ η` (`Endpoints.lean:~190`), hypothesis text of `queX_core` is `QDiff`'s second conjunct verbatim | `z = E + iη_Q ∈ locDomain κ ε_Q` (`N^{-1+ε_Q} ≤ η_Q ≤ 1`); `η_Q = W^{-ε₀}lam W^{d/2}/N` | at `sz0, n=0`: `η_Q N = 2.52`, so `N^{ε_Q} ≤ 2.52` needs `ε_Q ≲ 0.063` (MA-05b's choice, not this ticket's) |
| MA-05b chain (symbolic, `d` general) | `N²η_Q² K = C W^{-2ε₀}`; `Nη_Q·B_{η_Q,0} ≤ 2` since `Nη_Q/(lam²W^d) = W^{-ε₀}lam⁻¹W^{-d/2} ≤ W^{-ε₀−𝔡}` by `lam ≥ W^{-d/2+𝔡}` (`(eq:WO)`) | gives `W^{-2ε₀+2c} + W^{τ+2c}(W^{-2𝔡/5} + W^{ε₀−𝔡})` after Markov: `1_2:539-543` | not a target here |

### (ii) One concrete nondegenerate instance

Data: `d = 3`, `sz0` (`Defs/Sizes.lean:260`, `n = 0`: `L = 4`, `W = 32`, `lam = 1/64`, `N = 2097152`), `𝔡 = κ = 1/10`,
`ε₀ = 1/30`, `c = 1/60`, `E = 0`, `η = 1`, `a = 0`, `z = zI = 1/2 + i N^{-4/5}`, core: `c_u = δ_{u,0}`.
Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2240/inst.py` (script 3; scripts 1, 4 are `pre.py`, `theta.py` in the same directory). Output (verbatim):
```
sz0 n=0: W,L,lam,N = 32 4 0.015625 2097152
0<e0<dd/2: True  0<c<e0: True  c<dd/5: True  (eq:WO) W^(-d/2+dd)<=lam<=1/dd: True
window half-width = 1.201554345984338e-06 <= eta=1 : True   slack factor = 832255.3227343033
threshold W^(-2c) = 0.8908987181403393  ; W^(d-c)/N = 0.014748036135651463  ; W^-d*W^(d-c)/N squared*N^2 = 0.8908987181403396
zI = 1/2 + i N^(-4/5): Im z = 8.763872947670244e-06  0<Im<=1: True  |Re z|<=2-kap: True
thetaDiff: d>=3, L=4>=3, 0<g=1/64<=1/dd=10: True
|m|^2 = 0.999990948751903  1-|m|^2 = 9.051248097025066e-06  Im z^-2 = 13019906166.335155
core instance (sz0,n=0,z=zI,c=delta_0): eps := 13020016648.336012  K := 220964.00171125054  bound 4(K+eps) = 52080950449.35089
eta_Q (E any, e0=1/30) = 1.201554345984338e-06  <= Im zI: True
```
Hypotheses of each target at this data:
- `inst_thetaDiff` (`MAThetaDiff`): `d = 3 ≥ 3`, `𝔡, κ > 0`, `L = 4 ≥ 3`, `0 < 1/64 ≤ 10`, `0 < Im zI ≤ 1`, `|Re zI| = 1/2 ≤ 19/10`: all True above; `a = 0`, `b, b'` arbitrary in `Zd 3 4` (64 points).
- `inst_queBad_sub`: `η = 1 > 0`; window hypothesis `h = 1.2e-6 ≤ 1` for every `x` with `|x − 0| ≤ h`; `a` arbitrary in `Zd 3 4`; no hypothesis on `ε₀, c` (the pin has none; the values above also satisfy `QUE`'s ranges `0 < ε₀ < 𝔡/2`, `c < ε₀ ∧ 𝔡/5`).
- `que2Bad_sub`: same window; `A` nonempty (any, e.g. `{0}`); (no instance is required by the ticket).
- `queX_core` (not an endpoint, no instance required; hypotheses are satisfiable with finite numbers): `Im zI > 0`; `ε := (Im z)^{-2} + (1−|m|²)⁻¹` (bound on `‖∫avg2 |G|² − profPM‖ ≤ (Im z)^{-2} + ‖msc z‖²‖Θ_ab‖/W^d`, with `‖Θ‖ ≤ (1−‖ξ‖)⁻¹` for `‖S^B‖ = 1`, `|G_xy| ≤ (Im z)⁻¹`; same for `profPP`); `K := 2(1−|m|²)⁻¹`; `c = δ_0` is `≥ 0` with `Σ c = 1`. Numbers above.
- `normSq_le_trace`, `queMarkov`: general `ι`, `H`, `P`, `f`; hypotheses are an eigenbasis, `η > 0`, `B = B^*`, window; satisfied by script 1's random `H` (216 × 216, `E = 0.3`, `η = 0.05`, 11 eigenvalues in the window).

External-hypothesis limit computation (TEAM §8 lesson 14): none of the targets has an external hypothesis; `MAThetaDiff` is proved from the merged `prop5to8_holds` (no hypothesis). Numeric check of `thetaDiff`'s truth at the instance (script 4, `d = 3`, `L = 4`, `g = 1/64`, `z = zI`, `S^B` built from `sbKernel`, `Defs/Block.lean:38-44`):
```
z = (0.5+8.763872947670244e-06j)  m = (-0.24999886858886752+0.968241454625957j)  |m| = 0.9999954743657108  m^2+zm+1 = 2.220446049250313e-16
row sums (doubly stochastic): 0.9999999999999999 0.9999999999999999
(+,-) xi=|m|^2 : |xi| = 0.999990948751903  max|T_0b-T_0b'| = 878.853245803863  g^-2 = 4096.0  ratio = 0.21456378071383375
(+,+) xi=m^2 : |xi| = 0.999990948751903  max|T_0b-T_0b'| = 0.5168411284252904  g^-2 = 4096.0  ratio = 0.00012618191611945566
```
(`max|ΔΘ|` is finite and `≤ 0.22·g^{-2}` even at `1 − |ξ| = 9.05e-6`: the zero mode cancels in the difference.)

Script 1 (`pre.py`, `d = 3`, `W = 2`, `L = 3`, `N = 216`, random Hermitian `H`, `z = 0.3 + 0.05i`; parts B–D) output, verbatim:
```
X_c = (0.0022439230612966237+6.918375623833963e-21j)  formula = (0.0022439230612966215-0j)  |diff|= 2.168415381611748e-18  Im X= 6.918375623833963e-21
sum|beta| = 0.4563005179232426  <=2; sum beta = 1.5959455978986625e-16
eigenvalues in [E-eta,E+eta]: 11
max normSq/(4 eta^2 X_a) over window pairs = 0.007891074678542314  (<=1)
que2 identity and (ssfa2) bound OK on window; X_B>=0: True  X_a>=0: True
max |profile part|/K over random profiles = 0.25798029394483524  (<=4)
```
(The asserts inside script 1 check `ψ_i^*B_{δ_a}ψ_j = W^{-d}(Σ_{x∈[a]} ψ̄_iψ_j − (W^d/N)δ_ij)` and the `1_A/|A|` identity to `1e-12` for all window pairs.)

### Verdict per target

- `MAThetaDiff` / `thetaDiff` (verbatim probe `:665-772`) vs `1_2:536-537` (`max |Θ_ab − Θ_ab'| ≺ ilambda^{-2}`): PASS. The pin is the deterministic form with constant `C(d, 𝔡, κ)` (no `≺`, no `W^τ`): stronger than the paper's `≺`; it is already compiled in the probe from merged `prop5to8_holds`. Differences are D500/D503/D504 territory (`docs/paper-deltas.md:1459-1463`), not re-proposed. No `T2240a`.
- `inst_thetaDiff`: PASS (all hypotheses True at the instance).
- `normSq_le_trace`: PASS (derivation in table; the pin's `|μ_k − E| ≤ η`, `|μ_k' − E| ≤ η`, `B^* = B`, `η > 0` are exactly what the proof uses; `IsOrthoEigenbasis` gives `H = U diag(μ) U^*`, `μ` real, `z = E + iη` so `μ − z ≠ 0`).
- `queMarkov`: PASS (`P{s ≤ f} ≤ s⁻¹∫f ≤ T/s`; `T ≥ ∫f ≥ 0`).
- `queX_core`: PASS. Constant `4(K + ε)` verified by the count in the table (`¼·16K`, `¼·16ε`); hypothesis form is `QDiff`'s second conjunct with `ε` in place of `qdBoundExp`; the row-difference hypothesis is in the second index, as the reduction needs.
- `queBad_sub`, `que2Bad_sub`: PASS (threshold `W^{-2c} ≤ 4N²η²X` exact; no hypothesis on `ε₀, c`; the window hypothesis form `∀ x, queWindow … x → |x−E| ≤ η` is what the inclusion `μ_i, μ_j ∈ window ⇒ |μ − E| ≤ η` uses).
- `inst_queBad_sub`: PASS (window `1.2e-6 ≤ 1`; `sz0` values are `32, 4, 1/64, 2097152`).
- §29 (1) no time; (2) no case-(ii) boundary; (3) `3 ≤ d` only inside `MAThetaDiff` (`Sizes d` carries `3 ≤ L`); (4) no `∀ᶠ`, no `∀ n`; (5) `a`, `A`, `i, j` inside the events (inherited from `queBadMat`/`que2BadMat`); (6) `η > 0`, `0 < Im z` explicit; (7) scales `W^{-d}`, `L^{-d}`, `N = (WL)^d` (`Sizes.size`), no `log L`. §64 (4): not triggered. "Two data, one model": `queX`, `Gn`, `seqXmat` are all functions of `(d, sz, n, z, c)` on the same `seqP sz`: PASS. Registry: `queBadMat` is already structural (`Axioms.lean:302`); `que2BadMat` occurs only inside a set-builder; no owed line is touched.
- Overall: PASS. No false pin found.

## (a′) Preflight corrections — Tue Oct  6 02:26:23 UTC 2026
One index slip in the trace-algebra row of (i), no verdict change: `tr(G E_u G^* E_v) = W^{-2d} Σ_{x∈[v], y∈[u]} |G_xy|² = T₋(v,u)`, not `T₋(u,v)`
(`E_u` sits between `G` and `G^*`, the row index of `G_xy` runs over `[v]`); likewise `tr(G^* E_u G E_v) = T₋(u,v)`. The four-term formula of (i) contains both `T₋(v,u)` and `T₋(u,v)`, so it, the constant `4(K+ε)` and the verdicts are unchanged.

## (b) Script output — Tue Oct  6 02:26:23 UTC 2026
Branch `t/T2240` in worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2240`, head 61862e8; `RBM3D/Main/QUECore.lean` has 1235 lines.

### Build, registry pre-check, full build
```
$ lake build RBM3D.Main.QUECore 2>&1 | grep -E "QUECore|^Build completed|error"
Build completed successfully (3715 jobs).
[exit 0]
$ printf "import RBM3D\nimport RBM3D.Main.QUECore\n#assert_rbm_axioms\n" > precheck.lean; lake env lean precheck.lean
axiom audit: 6973 theorems, 2358 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 128 (borrowed 1, owed 89, structural 32, refuted 6).
[exit 0]
$ lake build 2>&1 | grep -E "^(Build completed|error)"
Build completed successfully (4043 jobs).
[exit 0]
```

### `#print axioms` of every new public declaration, hygiene
```
$ lake env lean axioms.lean   (#print axioms, 8 declarations)
'RBM.Endpoints.thetaDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.normSq_le_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.queMarkov' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.queX_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.queBad_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.que2Bad_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Inst.inst_thetaDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Inst.inst_queBad_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
[exit 0]
$ grep -nE "sorry|admit|native_decide|^axiom|^ *axiom " RBM3D/Main/QUECore.lean; echo "grep hits: $(grep -cE "sorry|admit|native_decide|^axiom|^ *axiom " RBM3D/Main/QUECore.lean)"; git diff --stat main...t/T2240
grep hits: 0
 RBM3D/Main/QUECore.lean | 1235 +++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean  |    3 +-
 2 files changed, 1237 insertions(+), 1 deletion(-)
[exit 0]
```

### Verbatim and check-file equality (acceptance criteria)
```
$ python3 (probe 97d958e lines 665-772 and 2439-2446: `block in text`)
probe :665-772 in QUECore.lean: True
probe :2439-2446 in QUECore.lean: True
$ lake env lean checkeq.lean > out; grep -c error out   (check-file imports + `import RBM3D.Main.QUECore` + check file + 13 `example`s: 4+1 `rfl`, 6 targets, 2 instances)
0
[exit 0]
```

### Target statements (extracted from the file by script; `:= by` omitted)
```
-- RBM3D/Main/QUECore.lean:76
def MAThetaDiff : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔡 κ : ℝ, 0 < 𝔡 → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ 𝔡⁻¹ →
      ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → |z.re| ≤ 2 - κ → ∀ a b b' : Zd d L,
        haveI : NeZero L := ⟨by omega⟩
        ‖Theta d L g (((‖msc z‖ ^ 2 : ℝ)) : ℂ) a b - Theta d L g (((‖msc z‖ ^ 2 : ℝ)) : ℂ) a b'‖ ≤
            C * (g ^ 2)⁻¹ ∧
        ‖Theta d L g (msc z ^ 2) a b - Theta d L g (msc z ^ 2) a b'‖ ≤ C * (g ^ 2)⁻¹
-- RBM3D/Main/QUECore.lean:105
theorem thetaDiff : MAThetaDiff
-- RBM3D/Main/QUECore.lean:422
theorem normSq_le_trace {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (μ : ι → ℝ)
    (ψ : ι → ι → ℂ) (hψ : IsOrthoEigenbasis H μ ψ) (E η : ℝ) (hη : 0 < η) (B : Matrix ι ι ℂ)
    (hB : Bᴴ = B) (k k' : ι) (hk : |μ k - E| ≤ η) (hk' : |μ k' - E| ≤ η) :
    Complex.normSq (star (ψ k) ⬝ᵥ (B *ᵥ ψ k')) ≤
      4 * η ^ 2 * (Matrix.trace (queImG H ((E : ℂ) + (η : ℂ) * Complex.I) * B *
        queImG H ((E : ℂ) + (η : ℂ) * Complex.I) * B)).re
-- RBM3D/Main/QUECore.lean:1087
theorem queMarkov {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf : Integrable f P) (hf0 : ∀ ω, 0 ≤ f ω) {s T : ℝ} (hs : 0 < s)
    (hT : ∫ ω, f ω ∂P ≤ T) (S : Set Ω) (hS : S ⊆ {ω | s ≤ f ω}) :
    P S ≤ ENNReal.ofReal (T / s)
-- RBM3D/Main/QUECore.lean:805
theorem queX_core {d : ℕ} (sz : Sizes d) (n : ℕ) (z : ℂ) (hz0 : 0 < z.im) (ε K : ℝ)
    (hQ : ∀ a b : Zd d (sz.L n),
      ‖(∫ ω, avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP sz)) -
          profPM sz n z a b‖ ≤ ε ∧
      ‖(∫ ω, avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) a b ∂(Sizes.seqP sz)) -
          profPP sz n z a b‖ ≤ ε)
    (hK : ∀ a b b' : Zd d (sz.L n),
      ‖profPM sz n z a b - profPM sz n z a b'‖ ≤ K ∧ ‖profPP sz n z a b - profPP sz n z a b'‖ ≤ K)
    (c : Zd d (sz.L n) → ℝ) (hc0 : ∀ u, 0 ≤ c u) (hc1 : ∑ u, c u = 1) :
    Integrable (queX sz n z c) (Sizes.seqP sz) ∧ (∀ ω, 0 ≤ queX sz n z c ω) ∧
      ∫ ω, queX sz n z c ω ∂(Sizes.seqP sz) ≤ 4 * (K + ε)
-- RBM3D/Main/QUECore.lean:966
theorem queBad_sub {d : ℕ} (sz : Sizes d) (n : ℕ) (ε₀ c E η : ℝ) (hη : 0 < η)
    (hwin : ∀ x : ℝ, queWindow d (sz.L n) (sz.W n) (sz.lam n) ε₀ E x → |x - E| ≤ η)
    (a : Zd d (sz.L n)) :
    {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E a (sz.seqXmat n ω)} ⊆
      {ω | ((sz.W n : ℕ) : ℝ) ^ (-(2 * c)) ≤
        4 * Nsz sz n ^ 2 * η ^ 2 *
          queX sz n ((E : ℂ) + (η : ℂ) * Complex.I) (fun u => if u = a then 1 else 0) ω}
-- RBM3D/Main/QUECore.lean:1013
theorem que2Bad_sub {d : ℕ} (sz : Sizes d) (n : ℕ) (ε₀ c E η : ℝ) (hη : 0 < η)
    (hwin : ∀ x : ℝ, queWindow d (sz.L n) (sz.W n) (sz.lam n) ε₀ E x → |x - E| ≤ η)
    (A : Finset (Zd d (sz.L n))) (hA : A.Nonempty) :
    {ω | que2BadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E A (sz.seqXmat n ω)} ⊆
      {ω | ((sz.W n : ℕ) : ℝ) ^ (-(2 * c)) ≤
        4 * Nsz sz n ^ 2 * η ^ 2 *
          queX sz n ((E : ℂ) + (η : ℂ) * Complex.I)
            (fun u => if u ∈ A then ((A.card : ℝ))⁻¹ else 0) ω}
```

### Compiled nonempty instances (RBM3D/Main/QUECore.lean, `namespace RBM.Endpoints.Inst`)
```
-- :1112
theorem inst_thetaDiff : ∃ C : ℝ, 0 < C ∧ ∀ b b' : Zd 3 4,
    ‖Theta 3 4 (1 / 64) (((‖msc zI‖ ^ 2 : ℝ)) : ℂ) 0 b - Theta 3 4 (1 / 64) (((‖msc zI‖ ^ 2 : ℝ)) : ℂ) 0 b'‖ ≤
        C * ((1 / 64 : ℝ) ^ 2)⁻¹ ∧
      ‖Theta 3 4 (1 / 64) (msc zI ^ 2) 0 b - Theta 3 4 (1 / 64) (msc zI ^ 2) 0 b'‖ ≤ C * ((1 / 64 : ℝ) ^ 2)⁻¹
-- :1146
theorem inst_queBad_sub : ∀ a : Zd 3 (sz0.L 0),
    {ω | queBadMat 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (1 / 30) (1 / 60) 0 a (sz0.seqXmat 0 ω)} ⊆
      {ω | ((sz0.W 0 : ℕ) : ℝ) ^ (-(2 * (1 / 60 : ℝ))) ≤
        4 * Nsz sz0 0 ^ 2 * (1 : ℝ) ^ 2 *
          queX sz0 0 (((0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)
            (fun u => if u = a then 1 else 0) ω}
-- example :1157  [que2Bad_sub, A = {0}]
example := que2Bad_sub sz0 0 (1 / 30) (1 / 60) 0 1 one_pos queCore_inst_window ({0} : Finset (Zd 3 (sz0.L 0)))
  (Finset.singleton_nonempty _)
-- example :1169  [normSq_le_trace, Fin 2, H = diag(1/2,-1/2), B = σ_x, k=0, k'=1]
  refine normSq_le_trace (Matrix.diagonal (fun k : Fin 2 => if k = 0 then (1 / 2 : ℂ) else -(1 / 2)))
    (fun k => if k = 0 then 1 / 2 else -(1 / 2)) (fun k => Pi.single k 1) ?_ 0 1 one_pos
    (!![0, 1; 1, 0]) ?_ 0 1 ?_ ?_
-- example :1185  [queMarkov, Fin 2, P = (1/2)·count, f i = i, s = 1, T = 1/2, S = {1}]
  refine queMarkov ((2 : ℝ≥0∞)⁻¹ • (Measure.count : Measure (Fin 2))) (fun i => ((i : ℕ) : ℝ))
    (Integrable.of_finite) (fun i => Nat.cast_nonneg _) one_pos ?_ {1} ?_
-- example :1218  [queX_core, sz0, n = 0, z = zI, c = δ_0 (hQ: expectation half of QDiff, kept as hypothesis)]
  refine ⟨C * ((sz0.lam 0 ^ 2)⁻¹) / ((sz0.W 0 : ℕ) : ℝ) ^ 3, queX_core sz0 0 zI zI_im_pos ε _ hQ ?_
    (fun u => if u = 0 then 1 else 0) (fun u => by split_ifs <;> norm_num) (by simp)⟩
```

### Name clash, ports, registry
```
$ grep -rnE "(def|theorem|lemma|abbrev|instance|structure|inductive) +(RBM\.Endpoints\.)?(Inst\.)?(queImG|queBlk|queObs|queX|MAThetaDiff|thetaDiff|normSq_le_trace|queMarkov|queX_core|queBad_sub|que2Bad_sub|inst_thetaDiff|inst_queBad_sub|theta_diff_of_row)\b" RBM3D --include='*.lean' | grep -v "^RBM3D/Main/QUECore.lean\|^RBM3D/Probe/" | wc -l; grep -rln "queCore_" RBM3D --include='*.lean' | grep -v "^RBM3D/Main/QUECore.lean" | wc -l
       0
       0
[exit 0]
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks log -1 --format=%h; git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Main/QUEFromQDiff.lean | tail -2
9e0f275
 RBM2D/Main/QUEFromQDiff.lean | 37 +++++++++----------------------------
 1 file changed, 9 insertions(+), 28 deletions(-)
[exit 0]
$ git diff main...t/T2240 -- RBM3D/Test/Axioms.lean | grep "^[+-] "| cut -c1-150
-   `RBM.Endpoints.qd2Bad] -- the bad event of `(eq:diffu2)` in `QDiff` (MA-01, `Endpoints.lean:148`); hypothesis of the deterministic cover lemma `qd
+   `RBM.Endpoints.qd2Bad, -- the bad event of `(eq:diffu2)` in `QDiff` (MA-01, `Endpoints.lean:148`); hypothesis of the deterministic cover lemma `qd
+   `RBM.Univ.queWindow] -- the energy window `𝓘_E(ε₀) = {x : |x - E| ≤ W^{-ε₀} (ilambda W^{d/2}/N)}` of `(eq:defIE)` (`1_2:409`): a condition on the 
[exit 0]
```

### Narrative
- Layout: `thetaDiff` block 62-171 (verbatim probe `:665-772` plus one header line); vocabulary; `Spectral` 197-418; `normSq_le_trace`;
  `TraceAlgebra` 430-516; `Observable` 520-589; `Integr` 593-730; `Core` 734-912; `Events` 916-1082; `queMarkov`; `namespace Inst`.
- Port: RBM2D `RBM2D/Main/QUEFromQDiff.lean` at `c9a24cf` (read only) `:38-263` Spectral, `:267-336` TraceAlgebra, `:338-396` Observable, `:503-640` Core, `:642-794` Events, `:798-808` Markov, with
  `Z2 L` → `Zd d L`, `L²` → `L^d`, `W²` → `W^d`, `Epaper` → `queBlk`, `trGEGE` → `avg2` of the entries of `Gn`. Not used: `:398-449` (`trGEGE` integrability, redone for `avg2`) and `:451-501` (`d = 2` Fourier bound; `thetaDiff` replaces it).
- New against RBM2D: (1) `queCore_trace_blk`/`_GG`/`_GGstar` write `tr(G E_u H E_v)` as block sums (index order of the `|G|²` term: (a′)); (2) integrability of the `avg2` terms: `‖Gn_xy‖ ≤ |Im z|⁻¹`
  (`norm_Gsig_le_inv_eta`, `norm_matrix_entry_le_opNorm`) and measurability (`continuous_green_of_isHermitian`, `continuous_Xmat`, `measurable_slice`); (3) `queCore_norm_double_sum_le`: RBM2D compares with one constant `p₀`
  (translation invariance of the `d = 2` profile); here the profile varies along rows by `K`, so `Σ_v β_v P(u,v) = Σ_v β_v (P(u,v) − P(u,u))` (`Σβ = 0`) gives `‖Σ β_uβ_v h‖ ≤ (Σ|β|)²(ε+K)`;
  (4) in `queX_core` the `T₋(v,u)` sum is re-indexed `u ↔ v` (`hswap`): `‖E X_c‖ ≤ (Σ|β|)²(ε+K) ≤ 4(K+ε)`; (5) the event inclusions use `W^{d-c} = W^d (W^c)⁻¹` (`queCore_rpow_sub`) and `queCore_sub_of_normSq`.
- Statements equal the check file (13 `example`s, exit 0). `normSq_le_trace`, `queMarkov` keep the pinned `ι : Type`, `Ω : Type`. Imports: exactly the five of the check file; no merged signature changed; private helpers `queCore_*`, `theta_diff_of_row`.
- Registry: the pre-check flagged `RBM.Univ.queWindow` (hypothesis `hwin` of `queBad_sub`, `que2Bad_sub`), not `que2BadMat`, and the ticket header expected no new line. One line appended to `structuralProps`
  (the energy window `𝓘_E(ε₀)`, a condition on an eigenvalue; DECISIONS §20 data-condition rule); the previous last line's `]` became `,`. No owed line touched.
- Instances beyond the two named ones are anonymous `example`s (no new public name): `que2Bad_sub` at `A = {0}`; `normSq_le_trace` on `Fin 2`, `H = diag(1/2, −1/2)`, `B = σ_x`; `queMarkov` on `Fin 2`, `P = (1/2)·count`;
  `queX_core` at `sz0`, `n = 0`, `z = zI`, `c = δ_0`: its `hQ` (expectation half of `QDiff`, another gate's pin) stays a hypothesis, the row-difference hypothesis is discharged from `thetaDiff` with `K = C (ilambda²)⁻¹ / W^3`, `‖msc zI‖ < 1`.
- The window hypothesis of `inst_queBad_sub` is discharged by the private `queCore_inst_window`: `32^{-1/30}·(1/64)·32^{3/2}/2097152 ≤ 1`.

## (c) Verified Mathlib names used by the new (non-ported) proofs (module via `getModuleIdxFor?`, script `mods.lean`)
- Finset.sum_ite_mem : Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
- Finset.univ_inter : Mathlib.Data.Finset.BooleanAlgebra
- Finset.sum_le_card_nsmul : Mathlib.Algebra.Order.BigOperators.Group.Finset
- Finset.measurable_sum : Mathlib.MeasureTheory.Group.Arithmetic
- Matrix.mul_diagonal : Mathlib.Data.Matrix.Mul
- Matrix.mulVec_diagonal : Mathlib.Data.Matrix.Mul
- Matrix.diagonal_conjTranspose : Mathlib.LinearAlgebra.Matrix.ConjTranspose
- Matrix.sub_mulVec : Mathlib.Data.Matrix.Mul
- Matrix.smul_mulVec : Mathlib.Data.Matrix.Mul
- Matrix.sum_mulVec : Mathlib.Data.Matrix.Basic
- Matrix.one_mulVec : Mathlib.Data.Matrix.Mul
- dotProduct_sub : Mathlib.Data.Matrix.Mul
- dotProduct_sum : Mathlib.Data.Matrix.Mul
- dotProduct_smul : Mathlib.Data.Matrix.Mul
- Real.rpow_sub : Mathlib.Analysis.SpecialFunctions.Pow.Real
- Real.rpow_neg : Mathlib.Analysis.SpecialFunctions.Pow.Real
- Real.rpow_mul : Mathlib.Analysis.SpecialFunctions.Pow.Real
- Real.rpow_two : Mathlib.Analysis.SpecialFunctions.Pow.Real
- Real.rpow_le_one_of_one_le_of_nonpos : Mathlib.Analysis.SpecialFunctions.Pow.Real
- Real.rpow_le_rpow_of_exponent_le : Mathlib.Analysis.SpecialFunctions.Pow.Real
- Complex.conj_mul' : Mathlib.Analysis.Complex.Basic
- Complex.sq_norm : Mathlib.Analysis.Complex.Norm
- MeasureTheory.Integrable.of_bound : Mathlib.MeasureTheory.Integral.IntegrableOn
- MeasureTheory.Integrable.of_finite : Mathlib.MeasureTheory.Function.L1Space.Integrable
- MeasureTheory.Measure.count_apply : Mathlib.MeasureTheory.Measure.Count
- MeasureTheory.integral_count : Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
- MeasureTheory.integral_smul_measure : Mathlib.MeasureTheory.Integral.Bochner.Basic
- MeasureTheory.mul_meas_ge_le_integral_of_nonneg : Mathlib.MeasureTheory.Integral.Bochner.Basic
- Continuous.matrix_elem : Mathlib.Topology.Instances.Matrix
- Measurable.pow_const : Mathlib.MeasureTheory.Group.Arithmetic
- integral_conj : Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
- integral_re : Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
- Names verified absent: none looked up.

## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none (no `T2240a`). The explicit constants `4` in `(ssfa2)` and `4(K+ε)` in the core instantiate the paper's `≲` (D504, explicit form); the statements agree with `1_2:524-537`; D500, D503, D504 not re-proposed.
- Registry: one structural line, `RBM.Univ.queWindow` (above). The hub unions it with sibling edits of `RBM3D/Test/Axioms.lean` at merge (DECISIONS §20 (3)); until the root imports this module the full `lake build` does not scan it (pre-check above does).
- `queX_core` is conditional on the expectation half of `QDiff` (`hQ`, MA-05b supplies it at `η_Q` from `QDiff`) and on the row differences `K` (`thetaDiff` gives `K = C ilambda^{-2} W^{-d}`); its example keeps `hQ` as a hypothesis.
- MA-05b needs MA-01's private `W_pos_real`, `L_pos_real`, `size_cast` re-declared privately (ticket header); this file does not use them.
- Preflight (a): one index-order slip, corrected in (a′); no verdict changed.
