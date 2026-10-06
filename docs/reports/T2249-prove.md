Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 04:04:27 UTC 2026

Notation: `n = d m`, `u = u_t`, `S = Σ_{i≥1}|a_i-a_0|`, `ℓ = ℓ_u`, `C₅,c₅` = constants of `Prop5Decay d Λ` (`Propagator/Pins.lean:34`), `C(m)=(1+40dm)6^{dm}`.
Scripts (python only, no Lean): `S/T2249/t1.py t3.py t4.py t7.py`, `S = /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad`.

### (i) Exponent table
| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | T1 constant `C(m)` | `(1+40n)6^n` | `\|Φ'\|u ≤ (2/e+40n)e^{-uS/2}/z^n`; `\|u'\|≤u/(2(1-t))`; `z⁻¹≤6/ℓ` (`qa_Zinv_le`) | true constant `½(2/e+40n)6^n`; slack ≥ 2 (the `½`) + `(1-2/e)`; grid ratio `\|∂ϑ\|/bound ≤ 3.96e-5` |
| 2 | T1 rate `c₁` | `1/4` | `e^{-uS/2} ≤ e^{-S/(4ℓ)}` from `u ≥ (2ℓ)⁻¹` (`qaU_lb`) | exact (`qaU_ub`: `ℓu ≤ 2`) |
| 3 | `x e^{-x} ≤ (2/e)e^{-x/2}` | `2/e ≤ 1` | `x ≥ 0` | equality at `x=2` (max ratio 1.0, grid) |
| 4 | T2 window `S ≥ W^{ε'}ℓ/2` | `e^{-S/(4ℓ)} ≤ e^{-W^{ε'}/8}` | closing `C(m) W^{C₀+K+D'} ≤ e^{W^{ε'}/8}` (`qn_growth`, `c=1/4`) | `ℓ^{-n} ≤ 1`; true `S ≥ W^{ε'}ℓ` (two terms of the sum, all pairs) gives `e^{-W^{ε'}/4}`: slack factor 2 in the exponent |
| 5 | T3 constants | `C = 2C₅e^{c₅}`, `c = c₅` | `B_{u,K} ≤ (g²+1-u)⁻¹+(L^d(1-u))⁻¹ ≤ 2(1-u)⁻¹` (`(K+1)^{d-2} ≥ 1`, `L^d ≥ 1`); `\|y-z\| ≥ \|y-x\|-1`, `ℓ ≥ 1` (`one_le_ellT`) | `e^{c₅/ℓ} ≤ e^{c₅}`; `(C₅,c₅)` depend on `(d,Λ)` only, not on `L,g≤Λ,u,μ` |
| 6 | T3 sqrt of `μ` | `m·m = μ`, `‖m‖=1` | `PropSpin m true · PropSpin m true = μ`, `t(m·m) = uμ` | exists for every `‖μ‖=1` (T3, T4, T5 any sign pair) |
| 7 | T4 `W^ε ≥ 2` | `W₀ ≥ 2^{1/ε}` | far case: `\|a_i-b\| ≥ W^{2ε}ℓ-W^εℓ ≥ W^{2ε}ℓ/2` | equality at `W^ε=2` (t4.py uses exactly `R2=2R1`) |
| 8 | T4 `W ≥ 2n` | `W₀ ≥ 2n` | `nW^{K-D} ≤ ½W^{K+1-D}` | slack `W/(2n)` |
| 9 | T4 closing | `2nC W^{2K+C₀+D} ≤ e^{cW^{2ε}/2}` | far sum: `≤ n·L^d·(C(1-u)⁻¹)·W^{C₀}·e^{-cW^{2ε}/2}`, `L^d ≤ W^K`, `(1-u)⁻¹ ≤ W^K` | `qn_growth` at `(ε'→2ε, p = 2K+C₀+D)`; `W₀` after `(d,n,Λ,K,C₀,ε,D)`, `C,c` from T3 |
| 10 | T4/T5 loss | `K+1` | near: `Σ_b\|K_i(a_i,b)\| ≤ (1-u)⁻¹ ≤ W^K` (`B45_row_thetaKer`), `\|A\| ≤ W^{-D}`; total `nW^{K-D}+(far) ≤ W^{K+1-D}` | independent of `ε, D` |
| 11 | T5 | `L=sz.L n`, `g=sz.lam n`, `W=sz.W n` | `3 ≤ sz.L n` is the field `Sizes.three_le_L` (`Defs/Sizes.lean:145`); `‖mSigma E b‖=1` for `\|E\|≤2` | no new constants |
| 12 | times | `0 ≤ t<1`, `0 ≤ u<1` | `Theta` needs `‖uμ‖=u<1`; `(1-u)⁻¹` finite | no `lemT`, no `1-u ≥ λ²/L²` used |

§29/§45 O2 checklist: (1) times `0≤t,u<1` only. (2) scale `ℓ_t=ellT L g t` in T1, T2; `ℓ_u` in T3, T4, T5, same `u` in and out. (3) `L^d ≤ W^K`, `(1-u)⁻¹ ≤ W^K` (T2 only the second), `‖A‖,‖B‖ ≤ W^{C₀}` explicit hypotheses. (4) `W₀` after `(ε,D,C₀,K)`; loss `K+1` fixed before them. (5) `g ≤ Λ` only T3-T5; T1, T2 any `g>0`. (6) no `𝒬`, no restriction on `σ`/`μs` beyond `‖μ_i‖=1`.

Route check against the paper (`paper/tex/3_5_Loop_Hierarchy.tex`): `(eq:derv_Theta)` `:1215` gives for `∂_tϑ` only `≺ |1-t|⁻¹(ℓ^d)^{-(n-1)}` (no exponential), `rmk:choosechi` `:1250`, `(def:op_thn)` `:111`, `lem_+Q` `:1285`; `(eq:THETAinftinf)` `1_2:1141`. The decay half of `∂_tϑ` is not in the paper text (T1 proves it for the explicit `ϑ*`; paper-delta T2239a/D556).
**Property 5 (required line):** merged form `Prop5Decay d Λ` (`Pins.lean:34-46`): `‖Θ_{t·PropSpin m σ₁·PropSpin m σ₂}(0,a)‖ ≤ C·Bparam d L g t |a|·exp(-c|a|/ℓ_t)`, `g ≤ Λ`, all `‖m‖=1`, all sign pairs, no bulk condition; proved as `prop5Decay_holds` (`Prop5Hold.lean:784`, "No unproved input"), bundled in `prop5to8_holds` (`Prop6Hold.lean:433`).
Copy list: dependency closure of `qa_deriv_real`/`qa_core`/`qa_Zinv_le`/`qaU_lb`/`qa_inv_pow_eq` is exactly the ticket's ranges (`grep` of names per range, `QopAlgebra.lean:40-131,136-245,247-286,332-343,377-408,410-437,439-458,460-505,506`); `qaZ1_pow :287`, `qa_sum_filter_prod :300` are used only by `QopAlgebra_mollifier_sum` and are not needed. `qn_growth` (`QopNorm.lean:343`) has the form `C W^p ≤ exp(c W^{ε'}/2)`. `qdec_mollifier_eq` is `rfl` as claimed by the ticket (`QopAlgebra_mollifier` is `((qaPhi d L m a (qaU L g t) : ℝ) : ℂ)`, `:345`).
Registry: no new `Prop`; `RBM.EKFastDecay` is in `structuralProps` (`Test/Axioms.lean:287`; the ticket says `:280`).

### (ii) Nondegenerate instance (all hypotheses hold at once; kernel constants `(C,c)=(1,1/4)` are an empirical stand-in, see below)
T1 / T2 (derivative identity and bound), exhaustive in `S`, `d∈{3,4}`, `m∈{1,2,3}`, `L∈{3,5,16}`, `g∈{.1,1,5}`, `t∈{0,.1,…,.9,.99,.999}`:
```
$ python3 S/T2249/t1.py | tail -3
cases 17280 max ratio |d_t theta|/bound = 3.9593443653616894e-05 at (d,m,L,g,t,S)= (3, 1, 16, 5.0, 0.9, 0)
max rel diff finite-diff vs analytic Phi'(u)u' (cases with |an|>0): 1.5775925451389975e-22
max (x e^-x)/((2/e)e^{-x/2}) on [0,50] = 1.0 at x= 2.0
```
T3 (no external hypothesis: `prop5Decay_holds` is merged; this is the numerical limit check of `max|thetaKer|(1-u)e^{c|y-x|/ℓ_u}`, `Θ=(1-uμS)⁻¹`, `d=3`, `u∈{0,.5,.9,.99}`, `μ∈{1,i,e^{iπ/3}}`; `L=8,12` give identical values):
```
$ python3 S/T2249/t3.py
d=3 L=8 g=0.5: max_(u,mu,y) |K(0,y)|(1-u)e^(c|y|/ell_u) = {0.1: 0.4, 0.25: 0.4, 0.5: 0.4, 1.0: 0.4}
d=3 L=8 g=2.0: max_(u,mu,y) |K(0,y)|(1-u)e^(c|y|/ell_u) = {0.1: 0.168, 0.25: 0.181, 0.5: 0.205, 1.0: 0.264}
```
(`0.4 = (1+2dg²)⁻¹` at `g=.5` is `K(0,0)`; bounded for `c` up to 1, so `(C,c)=(1,1/4)` is admissible here; `SB` row sums = 1 checked.)
T4 combinatorics (near/far split, extremal `R2 = 2·R1`, brute force over all `(a,i,b)`; "violating" = `a,i` with a far `b` such that `i∉{j,k}` or `|a_i-b| < R2/2`):
```
$ python3 S/T2249/t4.py      # configs (d,L,n,R1)
(2, 7, 3, 2) (a,i,b) triples, far triples, violating (a,i): (14434812, np.int64(52920), 0)
(2, 7, 3, 1.5) (a,i,b) triples, far triples, violating (a,i): (16595712, np.int64(74676), 0)
(3, 7, 2, 2) (a,i,b) triples, far triples, violating (a,i): (65883440, np.int64(1344560), 0)
(3, 9, 2, 1.5) (a,i,b) triples, far triples, violating (a,i): (748268928, np.int64(7185024), 0)
(1, 15, 3, 3) (a,i,b) triples, far triples, violating (a,i): (89100, np.int64(4320), 0)
```
Concrete data for T4, T5 (`n=2`, `Fin 2` as `STthetaOp`; for T5: `sz.L n = 500`, `sz.W n = 23`, `sz.lam n = 1`, any `E` with `|E|≤2`, any `σ`) and T2 (`m=1`), minimal `W` found by search, window forced non-empty:
```
$ python3 S/T2249/t7.py
TARGET 4/5 instance: d=3 n=2 L=500 g=1.0 Lambda=1.0 u=0.5 eps=1.0 C0=0 K=6 D=8.0 W=23 (c=0.25, C=1.0)
 ell_u = 1.414213562373095 3<=L: True 0<g<=Lam: True 0<=u<1: True
 L^d = 125000000 <= W^K = 148035889 : True  (1-u)^-1 = 2.0 <= W^K: True
 W^eps = 23.0 >=2: True  W>=2n: True
 window: W^(2eps) ell = 748.119 <= d*floor(L/2) = 750 : True ; W^eps ell = 32.527
 closing: ln(2nC)+(2K+C0+D)lnW = 64.096 <= c W^(2eps)/2 = 66.125
 conclusion: |ThetaN A| <= W^-(D-(K+1)) = 0.043478260869565216
 pair at distance >= W^(2eps) ell: a=(0,(floor(L/2),)*3), |a0-a1| = 750
TARGET 2 instance: d=3 m=1 eps'=1.0 K=1 D'=1 C0=0 g=1.0 t=0.5 W=163 L=154: ln(C W^(C0+K+D')) = 20.36 <= W^eps'/8 = 20.38; window W^eps' ell = 230.5 <= d floor(L/2) = 231
   target 1 at S=231: |d_t theta| = 3.013e-43 <= bound 3.405e-14; target-2 value W^C0*bound(S>=W^eps' ell) = 7.405e-05 <= W^-D' = 6.135e-03
```
(The `eps'=0.5` line of the same output, `W=67192`, is omitted.) Reading: `|ΘN A|` has a non-empty region (`a` with a pair at distance `750 ≥ W^{2ε}ℓ_u`), every deterministic hypothesis holds (`3≤L`, `0<g≤Λ`, `0≤u<1`, `L^d ≤ W^K`, `(1-u)⁻¹ ≤ W^K`, `W^ε ≥ 2`, `W ≥ 2n`); `L` is large only because the window `W^{2ε}ℓ_u ≤ d⌊L/2⌋` and `L^d ≤ W^K` must both hold (`K=6`, `W=23`: no `N=0`, no collapsed window). Caveat: `(C,c)` of T3 are Lean-side existentials from `prop5Decay_holds`; the stand-in only fixes this instance's `W`; a `W` satisfying the closing inequality exists for every `(C,c)` since `W^p ≪ e^{cW^{2ε}/2}`.

### Verdicts
- Target 1 `QopAlgebra_mollifier_derivDecay`: PASS (statement true with the stated `C(m)`, `c=1/4`; identity `Φ'(u)=Φ(u)(-S+n z₂/z)` matches `qaPhi_hasDerivAt`; true for every `t<1`).
- Target 2 `QopDecay_deriv_fastDecay`: PASS (`W₀` depends on `(d,m,K,C₀,ε',D')`; no `L^d ≤ W^K` needed).
- Target 3 `QopDecay_thetaKer_decay`: PASS (all sign pairs via `m·m=μ`; constants `(d,Λ)`).
- Target 4 `QopDecay_ThetaN_fastDecay`: PASS (`n=0,1` vacuous; far case needs `i∈{j,k}`, verified by brute force; loss `K+1`).
- Target 5 `QopDecay_STthetaOp_fastDecay`: PASS (`3 ≤ sz.L n` from `Sizes.three_le_L`).
- Observations (not defects): (a) `EKFastDecay` registry line is `Axioms.lean:287`, not `:280`; (b) `S ≥ W^{ε'}ℓ` holds without the `½` (T2 closes with `e^{-W^{ε'}/4}` too); (c) the paper-delta candidates of the ticket (D556/T2239a derivative-decay half; `T2249a` `(deccA0)` propagation through `Θ^{(n)}_u`) are unchanged by this preflight.

## (b) Script output — Tue Oct  6 04:21 UTC 2026 (`date -u`), commit 03127a1 on `t/T2249`, file `RBM3D/Induction/QopDecay.lean` (1025 lines)

```
$ lake build RBM3D.Induction.QopDecay 2>&1 | tail -3

Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3777 jobs).
$ lake env lean (axioms file)  # #print axioms of the 5 targets
'RBM.Gauss.Sizes.QopAlgebra_mollifier_derivDecay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.QopDecay_deriv_fastDecay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.QopDecay_thetaKer_decay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.QopDecay_ThetaN_fastDecay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.QopDecay_STthetaOp_fastDecay' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
$ check-file equality: lake env lean eq_check.lean  (check file + import QopDecay + 5 `example : T2249Check.X := @X`)
eq exit 0
$ grep -c error eq_out.txt
0
$ registry pre-check (import RBM3D + import RBM3D.Induction.QopDecay + #assert_rbm_axioms): exit 0; diff against the same without the QopDecay import
1c1
< axiom audit: 7330 theorems, 2475 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
---
> axiom audit: 7335 theorems, 2475 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
161:premises found by scanning: 151 (borrowed 1, owed 100, structural 38, refuted 6, superseded 6).
0
$ full lake build with temporary root import of RBM3D.Induction.QopDecay (removed afterwards; git status shows RBM3D.lean unchanged)
Build completed successfully (4053 jobs).
$ git diff --stat main...t/T2249
 RBM3D/Induction/QopDecay.lean | 1025 +++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1025 insertions(+)
$ git diff main -- QopAlgebra.lean QopNorm.lean Step34Pins.lean | wc -l
       0
$ grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Induction/QopDecay.lean
0
```

Target statements (as in the file; they are the statements of the check-file section 2 defs, confirmed by the compiled `@X` equality above):
```
$ python3 extract-statements RBM3D/Induction/QopDecay.lean  # file:line of each target, text up to `:= by`
-- QopDecay.lean:497
theorem QopAlgebra_mollifier_derivDecay (d L m : ℕ) [NeZero L] (hL : 3 ≤ L) {g : ℝ} (hg : 0 < g)
    (t : ℝ) (_ht0 : 0 ≤ t) (ht : t < 1) (a : Fin (m + 1) → Zd d L) :
    ‖deriv (fun τ => QopAlgebra_mollifier d L m g τ a) t‖ ≤
      (1 + 40 * ((d * m : ℕ) : ℝ)) * 6 ^ (d * m) * (1 - t)⁻¹ * (((ellT L g t) ^ d)⁻¹) ^ m *
        Real.exp (-(1 / 4) * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)),
          (zdistD d L (a i - a 0) : ℝ)) / ellT L g t) :=
-- QopDecay.lean:514
theorem QopDecay_deriv_fastDecay (d m : ℕ) (K C₀ ε' D' : ℝ) (hε' : 0 < ε') :
    ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g →
      ∀ W : ℝ, W₀ ≤ W → ∀ t : ℝ, 0 ≤ t → t < 1 → (1 - t)⁻¹ ≤ W ^ K →
      ∀ B : Zd d L → ℂ, ‖B‖ ≤ W ^ C₀ →
        EKFastDecay g t W ε' D'
          (fun a : Fin (m + 1) → Zd d L => B (a 0) *
            deriv (fun τ => QopAlgebra_mollifier d L m g τ a) t) :=
-- QopDecay.lean:636
theorem QopDecay_thetaKer_decay (d : ℕ) (hd : 3 ≤ d) (Λ : ℝ) (hΛ : 0 < Λ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g → g ≤ Λ →
        ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ μ : ℂ, ‖μ‖ = 1 → ∀ x y : Zd d L,
          ‖thetaKer d L g μ u x y‖ ≤
            C * (1 - u)⁻¹ * Real.exp (-c * (zdistD d L (y - x) : ℝ) / ellT L g u) :=
-- QopDecay.lean:762
theorem QopDecay_ThetaN_fastDecay (d n : ℕ) (hd : 3 ≤ d) (Λ K C₀ ε D : ℝ) (hΛ : 0 < Λ) (hε : 0 < ε) :
    ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g → g ≤ Λ →
      ∀ W : ℝ, W₀ ≤ W → (L : ℝ) ^ d ≤ W ^ K →
      ∀ u : ℝ, 0 ≤ u → u < 1 → (1 - u)⁻¹ ≤ W ^ K →
      ∀ μs : Fin n → ℂ, (∀ i, ‖μs i‖ = 1) →
      ∀ A : (Fin n → Zd d L) → ℂ, ‖A‖ ≤ W ^ C₀ → EKFastDecay g u W ε D A →
        EKFastDecay g u W (2 * ε) (D - (K + 1)) (ThetaN d L g μs u A) :=
-- QopDecay.lean:883
theorem QopDecay_STthetaOp_fastDecay {d : ℕ} (hd : 3 ≤ d) (Λ K C₀ ε D : ℝ) (hΛ : 0 < Λ) (hε : 0 < ε) :
    ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| ≤ 2 → 0 < sz.lam n → sz.lam n ≤ Λ →
      W₀ ≤ ((sz.W n : ℕ) : ℝ) → ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K →
      ∀ u : ℝ, 0 ≤ u → u < 1 → (1 - u)⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ K →
      ∀ (σ : Fin 2 → Bool) (A : (Fin 2 → Zd d (sz.L n)) → ℂ), ‖A‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀ →
        EKFastDecay (sz.lam n) u ((sz.W n : ℕ) : ℝ) ε D A →
        EKFastDecay (sz.lam n) u ((sz.W n : ℕ) : ℝ) (2 * ε) (D - (K + 1)) (STthetaOp sz n E u σ A) :=
```

Compiled nonempty instances (one per target; `d = 3`, `L = 5`, `g = 1`, `u = t = 1/2`; every deterministic hypothesis discharged: `3 ≤ L`, `g ≤ Λ`, `L^d = 125 ≤ W^3`, `(1-u)⁻¹ = 2 ≤ W^3`, `‖A‖ ≤ W^0`, `EKFastDecay` of the nonzero tensor `qdecA` (supported on `b₀ = b₁`), `|μ| = 1`; `W` is chosen as `max W₀ 5`, `W₀` being the existential threshold):
```
$ python3 extract-examples  # the 5 compiled `example`s (statement up to the proof; proofs in the file; all compile in the build above)
-- QopDecay.lean:931
example : ‖deriv (fun τ => QopAlgebra_mollifier 3 5 1 1 τ ![0, fun _ => 1]) (1 / 2 : ℝ)‖ ≤
    (1 + 40 * ((3 * 1 : ℕ) : ℝ)) * 6 ^ (3 * 1) * (1 - (1 / 2 : ℝ))⁻¹ *
      (((ellT 5 1 (1 / 2 : ℝ)) ^ 3)⁻¹) ^ 1 *
      Real.exp (-(1 / 4) * (∑ i ∈ Finset.univ.erase (0 : Fin (1 + 1)),
        (zdistD 3 5 ((![0, fun _ => 1] : Fin 2 → Zd 3 5) i - (![0, fun _ => 1] : Fin 2 → Zd 3 5) 0) : ℝ)) /
          ellT 5 1 (1 / 2 : ℝ)) :=
-- QopDecay.lean:942
example : ∃ W : ℝ, 2 ≤ W ∧
    EKFastDecay (d := 3) (L := 5) (n := 2) 1 (1 / 2) W 1 1
      (fun a : Fin (1 + 1) → Zd 3 5 => (fun _ : Zd 3 5 => (1 : ℂ)) (a 0) *
        deriv (fun τ => QopAlgebra_mollifier 3 5 1 1 τ a) (1 / 2 : ℝ)) :=
-- QopDecay.lean:956
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ‖thetaKer 3 5 1 Complex.I (1 / 2 : ℝ) 0 (fun _ => 2)‖ ≤
      C * (1 - (1 / 2 : ℝ))⁻¹ * Real.exp (-c * (zdistD 3 5 ((fun _ => 2 : Zd 3 5) - 0) : ℝ) / ellT 5 1 (1 / 2 : ℝ)) :=
-- QopDecay.lean:966
example : ∃ W : ℝ, 5 ≤ W ∧
    EKFastDecay (d := 3) (L := 5) (n := 2) 1 (1 / 2) W (2 * 1) (1 - (3 + 1))
      (ThetaN 3 5 1 ![1, Complex.I] (1 / 2 : ℝ) qdecA) :=
-- QopDecay.lean:995
example : ∃ (N : ℕ) (hN : 0 < N), 5 ≤ N ∧
    EKFastDecay (d := 3) (L := (qdecSz N hN).L 0) (n := 2) ((qdecSz N hN).lam 0) (1 / 2)
      (((qdecSz N hN).W 0 : ℕ) : ℝ) (2 * 1) (1 - (3 + 1))
      (STthetaOp (qdecSz N hN) 0 0 (1 / 2) ![true, false] qdecA) :=
```

Name clash and prefix:
```
$ grep -rnE "QopDecay_|qdec|QopAlgebra_mollifier_derivDecay|T2249Check" RBM3D RBM3D.lean  # main worktree (main 9403c24), non-probe
hits:        0
$ grep -rnE "qd_" in the new file
       0
```

Ports (CLAUDE.md §5.2 does not apply: no RBM1D/RBM2D file was read or copied). Copies from RBM3D itself: private helpers of `RBM3D/Induction/QopAlgebra.lean` (last change on main `6b2494e`), lines 37-282, 331-340, 377-408, 438-458, 506-508, renamed `qa… -> qdec…` by `perl -pi -e 's/qa([A-Z_])/qdec$1/g'`; `qn_growth` (`QopNorm.lean:343-372`, last change `eb6d67a`) as `qdec_growth`; `qnA`, `qnA_ne`, `qnA_norm_le`, `qnA_fastDecay` (`QopNorm.lean:468-494`) as `qdecA…`. New: `qdec_core`, `qdec_deriv_real`, `qdec_mollifier_eq` (`rfl`), `qdec_sqrt_unit`, `qdec_sbKernel_support`, `qdec_Bparam_le`, `qdec_far_dist`, the five targets, `qdecSz`, the five examples. All helpers are `private`.

Narrative (every statement is a fact of the file or of the output above):
- Target 1: `qdec_core` is `qa_core` with `u S e^{-uS} ≤ e^{-uS/2}` (from `1 + y + y²/2 ≤ e^y` at `y = uS/2`, `2y ≤ e^y`) instead of `≤ 1`; the factor `e^{-uS/2}` is carried through `qdec_deriv_real` and replaced by `e^{-S/(4ℓ)}` with `qdecU_lb` (`u ≥ (2ℓ)⁻¹`). The constant is `(1+40dm)6^{dm}` (the `½` of `|u'| ≤ u/(2(1-t))` is dropped as in `QopAlgebra_mollifier_props`).
- Target 2: `stQop_sub_fastDecay` pattern with target 1 instead of the sup bound of `ϑ`: `S ≥ W^{ε'}ℓ/2` by the triangle inequality through `a₀`, `(ℓ^d)⁻¹)^m ≤ 1`, `(1-t)⁻¹ ≤ W^K`, `qdec_growth` at `c = 1/4`, `p = C₀ + K + D'`. No `L^d ≤ W^K`.
- Target 3: `prop5Decay_holds d Λ` at a unit square root `m` of `μ` (`IsAlgClosed.exists_pow_nat_eq`), signs `(+,+)`, `Theta` translation (`Theta_apply_add_right_of_three_le`), `Bparam ≤ 2(1-u)⁻¹`, `|y-z| ≥ |y-x| - 1` on the support `|x-z| ≤ 1` of `sbKernel`, row sum 1 (`sum_norm_SB_row`). Constants `C = 2 C₅ e^{c₅}`, `c = c₅`.
- Target 4: `qdec_far_dist` (brute-forced in section (a), now proved): if every pair of `a^{(i)}(b)` is `< r₁` and `(j,k)` is `≥ r₂ ≥ 2 r₁` then `|b - a_i| ≥ r₂/2`. Pointwise bound `‖K_i‖‖A‖ ≤ ‖K_i‖ W^{-D} + C W^{K+C₀} e^{-x}`, `x = c W^{2ε}/2`, summed with `B45_row_thetaKer` and `card = L^d ≤ W^K`. `W₀ = max W₁ (max 2^{1/ε} (2n))`, `W₁` from `qdec_growth` at `C' = 2(n+1)C`, `ε' = 2ε`, `p = K + C₀ + D - 1`. Loss `K+1` independent of `ε, D`; `n = 0, 1` need no special case.
- Target 5: `STthetaOp_eq_ThetaN`, `norm_mSigma`, `Sizes.three_le_L`; target 4 at `n = 2`.
- Windows: at `L = 5` the torus diameter is `3·2 = 6`, so for large `W` the window `W^ε ℓ` exceeds it and the conclusion of the examples is true because no `a` lies in the window; the content is in the proof (as in the `QopNorm.lean` instances). The nondegenerate numerical instance with a non-empty window is the one of section (a) (`L = 500`, `W = 23`, `K = 6`), checked by script there, not in Lean.
- No `Axioms.lean` hunk: the file defines no `Prop` and no theorem takes an unregistered `Prop`; the pre-check output differs from the baseline only in the theorem count (7330 -> 7335).
- Merge note for the hub: add `import RBM3D.Induction.QopDecay` after the last `import` of `RBM3D.lean` (currently `import RBM3D.Main.QUEFromQDiff`, line 289 of the worktree); no other file.

## (c) Mathlib names
Verified present by `grep` in `.lake/packages/mathlib/Mathlib/` and used: `Real.quadratic_le_exp_of_nonneg` (Analysis/Complex/Exponential.lean:263), `IsAlgClosed.exists_pow_nat_eq` (FieldTheory/IsAlgClosed/Basic.lean:81), `pow_eq_one_iff_of_nonneg` (used in Analysis/InnerProductSpace/PiL2.lean:975), `Function.update_self` (Logic/Function/Basic.lean:649), `Function.update_of_ne` (:653), `norm_le_pi_norm` (Analysis/Normed/Group/Constructions.lean:346), `inv_anti₀` (Algebra/Order/GroupWithZero/Basic.lean:1221). Others used (`Real.rpow_natCast`, `Real.rpow_add`, `Real.rpow_mul`, `Real.rpow_le_rpow`, `Real.exp_le_exp`, `pi_norm_le_iff_of_nonneg`, `Nat.le_ceil`, `Finset.sum_le_sum`, `norm_sum_le`, tactic `push Not` replacing the deprecated `push_neg`) are confirmed only by the successful build above. Names found absent: none.

## (d) Open issues and paper-delta candidates
- `T2249a` (candidate, as the ticket): `(deccA0)` propagation through `Θ^{(n)}_u` — `(u, ε, D) -> (u, 2ε, D - (K+1))` for `W ≥ W₀(d, n, Λ, K, C₀, ε, D)`, `L^d ≤ W^K`, `(1-u)⁻¹ ≤ W^K`, `‖A‖ ≤ W^{C₀}`, any unit charges — is used at `6:132` and `3_5:1711-1714` but not stated in the paper; proved here as `QopDecay_ThetaN_fastDecay`. The kernel decay `QopDecay_thetaKer_decay` (`|μ S Θ_{uμ}(x,y)| ≤ C (1-u)⁻¹ e^{-c|y-x|/ℓ_u}`) is also not stated.
- D556 / `T2239a` (derivative-decay half): `QopAlgebra_mollifier_derivDecay` makes explicit `|∂_tϑ_{t,a}| ≤ (1+40dm)6^{dm}(1-t)⁻¹(ℓ_t^d)^{-m} e^{-S/(4ℓ_t)}` for the explicit `ϑ*` (`rmk:choosechi`, `3_5:1250`; `(eq:derv_Theta)` `3_5:1215` gives only the size).
- Deviations from the ticket text: none in the statements. The ticket's `x e^{-x} ≤ (2/e) e^{-x/2}` is used in the weaker form `x e^{-x} ≤ e^{-x/2}` (constant `1` instead of `2/e`), enough for the stated `C(m)`. Section (a) observation (a): registry line of `EKFastDecay` is `Axioms.lean:287`, not `:280`.
- No hypothesis added, no target weakened, no file other than `RBM3D/Induction/QopDecay.lean` touched; no `T2249b`.

## Repair — Tue Oct  6 04:28:49 UTC 2026 (`date -u`), repairer claude-opus-5-5, commit 45d2123 on `t/T2249`

Addresses audit round 1 (`T2249-audit.md` §6, items 1–4: targets 4, 5 instances had a collapsed window). Only the
instance section of `RBM3D/Induction/QopDecay.lean` changed (hunks start at line 901, after the last target at 883);
no target statement changed. The (b) instances of targets 4, 5 at `QopDecay.lean:966/995` above are superseded by these.

```
$ git diff --stat 03127a1 HEAD
 RBM3D/Induction/QopDecay.lean | 171 +++++++++++++++++++++++++++---------------
 1 file changed, 112 insertions(+), 59 deletions(-)
$ git diff --stat main...t/T2249
 RBM3D/Induction/QopDecay.lean | 1078 +++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1078 insertions(+)
$ lake build RBM3D.Induction.QopDecay 2>&1 | tail -3
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3777 jobs).
$ lake env lean Eq.lean; echo "exit $?"   # check-file imports + import QopDecay + check §1–2 without #check + 5 `example : T2249Check.X := @RBM.Gauss.Sizes.X` + #print axioms
'RBM.Gauss.Sizes.QopAlgebra_mollifier_derivDecay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.QopDecay_deriv_fastDecay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.QopDecay_thetaKer_decay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.QopDecay_ThetaN_fastDecay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.QopDecay_STthetaOp_fastDecay' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" RBM3D/Induction/QopDecay.lean | wc -l
       0
$ grep -rnE "qdec_window|qdec_ellT_le" ~/Lean_proof/RBM3D/RBM3D | wc -l   # new helper names (both private)
       0
```

New compiled instances (statement text extracted by `awk` up to `:= by`; proofs in the file; built above):
```
-- QopDecay.lean:1009   (target 4: n = 2, Λ = 1, K = 4, C₀ = 0, ε = 1/4, D = 1, g = 1, u = 1/2, μs = (1, i), W = L = N)
example : ∃ (N : ℕ) (_ : NeZero N), 9 ≤ N ∧
    (∃ a : Fin 2 → Zd 3 N,
      (N : ℝ) ^ (2 * (1 / 4 : ℝ)) * ellT N 1 (1 / 2) ≤ (zdistD 3 N (a 0 - a 1) : ℝ)) ∧
    EKFastDecay (d := 3) (L := N) (n := 2) 1 (1 / 2) (N : ℝ) (2 * (1 / 4)) (1 - (4 + 1))
      (ThetaN 3 N 1 ![1, Complex.I] (1 / 2 : ℝ) (qdecA N)) := by
-- QopDecay.lean:1045   (target 5: same exponents, size data qdecSz N: L ≡ N, W ≡ N, λ ≡ 1; n = 0, E = 0, σ = (+, -))
example : ∃ (N : ℕ) (hN : 9 ≤ N),
    (∃ a : Fin 2 → Zd 3 ((qdecSz N hN).L 0),
      (((qdecSz N hN).W 0 : ℕ) : ℝ) ^ (2 * (1 / 4 : ℝ)) *
          ellT ((qdecSz N hN).L 0) ((qdecSz N hN).lam 0) (1 / 2) ≤
        (zdistD 3 ((qdecSz N hN).L 0) (a 0 - a 1) : ℝ)) ∧
    EKFastDecay (d := 3) (L := (qdecSz N hN).L 0) (n := 2) ((qdecSz N hN).lam 0) (1 / 2)
      (((qdecSz N hN).W 0 : ℕ) : ℝ) (2 * (1 / 4)) (1 - (4 + 1))
      (STthetaOp (qdecSz N hN) 0 0 (1 / 2) ![true, false] (qdecA N)) := by
-- QopDecay.lean:943    (the window conjunct of both, used at :1025 and :1063)
private theorem qdec_window (N : ℕ) (hN : 9 ≤ N) :
    ∃ a : Fin 2 → Zd 3 N,
      (N : ℝ) ^ (2 * (1 / 4 : ℝ)) * ellT N 1 (1 / 2) ≤ (zdistD 3 N (a 0 - a 1) : ℝ) := by
```

Narrative:
- In both examples `N := ⌈W₀⌉₊ + 9` is chosen after `W₀` (the statements quantify `L` after `W₀`), so `W₀ ≤ W = N`,
  `L^3 = N^3 ≤ N^4 = W^K`, `(1-u)⁻¹ = 2 ≤ N^4`, `‖qdecA N‖ ≤ 1 = W^0` are discharged in Lean.
- `qdecA N` (`b ↦ 1_{b₀ = b₁}` on `Zd 3 N`, nonzero by `qdecA_ne`) has `EKFastDecay 1 (1/2) N ε D` by `qdecA_fastDecay`.
- Window conjunct (`qdec_window`): `a = ((⌊N/2⌋,⌊N/2⌋,⌊N/2⌋), 0)` gives `zdistD = 3⌊N/2⌋`. It is proved from
  `ellT N 1 (1/2) ≤ 2` (`qdec_ellT_le`), `N^{2·(1/4)} = √N` and `3 ≤ √N`. This makes the conclusion window
  `W^{2ε} ℓ_u` nonempty. The hypothesis window `W^ε ℓ_u` is contained in it, because `W^ε ≤ W^{2ε}` for `W ≥ 1`;
  that inclusion is stated in the docstrings, not as a compiled conjunct.
- Audit O1 (optional, target 2) and O2, O3 are not changed.
