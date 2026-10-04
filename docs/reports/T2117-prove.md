Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 06:38:07 UTC 2026

Scripts (Python, no Lean) in `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2117/`: `env.py`, `inst.py`, `limit.py`, `ycheck.py`.
Source: RBM2D `Green/MinorDiffCond.lean` at `c9a24cf` (`git show`, 1464 lines; kept part = lines 1-912, `section Checks` 913-1387 not ported). Merged: `RBM3D/Green/MinorGoodLe.lean:751` (`MinorDiffGainUpTo'`), `:943` (`MinorGoodLe`).

### (i) Exponent table

Notation: `Ψ = 2δ_n` (δ = scale of the per-time good event `‖G_t − m‖_max ≤ δ`), `C_M = minorDiffC M`, `η = (1−t)·Im m_E`, `size = (WL)^d`.

| # | Quantity | Value | Constraint | Slack |
|---|---|---|---|---|
| 1 | Gain pair of `MinorDiffGainUpTo'` from the good event (MinorDiffCond:869-884) | `B = 2(2C_M Ψ + condCost)`, `ρ = 2Ψ`; at `ε = condEps`: `condCost = Ψ`, `B = 2(2C_M+1)Ψ` (`inst.py`: `condCost = Ψ` exactly) | `0 ≤ B`, `0 ≤ ρ`; `ρ < 1` iff `δ < 1/4` (`hδ4`) | `8Mδ ≤ 1` gives `ρ = 4δ ≤ 1/(2M) ≤ 1/2` for `M ≥ 1` |
| 2 | Layer `q ≤ M`: bound `B ρ^q` | `2(2C_M+1)Ψ(2Ψ)^q ∝ δ^{q+1}`; at `δ = W^{-c}`: `W^{-c(q+1)}`; paper floor `W^{-d/2} ≤ Ψ_t ≤ W^{-ε₀}` (`3_5:26-29`, `initialGT2`), so `c ∈ [ε₀, d/2]`, per-layer exponent `c`, sharp `c = d/2 = 3/2` at `d = 3` (RBM2D `d = 2`: `W^{-1}` per layer) | true size of `q`-th layer must be `≤ Bρ^q` | measured (iii): `rms|X_q| ∝ W^{-1.494, -2.955, -4.393}` for `q = 0,1,2` vs `-(q+1)d/2 = -1.5, -3, -4.5`; per-layer `-1.461, -1.437` vs `-1.5`: every layer `q ≤ 2` has exponent `d/2`, none steeper than `Bρ^q` allows |
| 3 | `C_M` (`atomC 0 = 2`, `atomC(r+1) = 16^r atomC(r)^5`, `C_M = 4^M atomC(M)^3`) | `C_0 = 8`, `C_1 = 131072 = 2^17`, `C_2 = 2^91` (`inst.py`) | depends on `M` only; no `d`, `W`, `L` (§29 constants rule) | none needed |
| 4 | `hB1: 2C_M Ψ + condCost ≤ 1`, at `ε = condEps`: `(2C_M+1)Ψ ≤ 1` | `δ ≤ 1/(2(2C_M+1))`: `M=1`: `δ ≤ 1/524290`; `M=2`: `δ ≲ 2^{-92}` | with `δ = W^{-c}`, `c = 3/2`: `W ≥ 6.5·10^3` (`M=1`), `W ≥ 4.6·10^{18}` (`M=2`); `c = 1`: `W ≥ 524290` (`M=1`) | holds for fixed `M,K,c` only eventually in `n` (asymptotic regime); free `δ` at a fixed slice: any `δ ≤` threshold. RBM2D has the same constants |
| 5 | `condEnv E t M = 2^{2M+1}(η⁻¹+1)` | `E=0,t=0,M=1`: `16`; `t=1/2`: `24` | needs `|E| < 2`, `t < 1` (`η > 0`) | `hB1` and `condCost(condEps)=Ψ` do not involve `η`; `η⁻¹` enters only `condEps` (`ε = Ψ(2Ψ)^M/((M+1)condEnv)`, `ε⁻¹ ∝ η⁻¹ W^{c(M+1)}`) and `hsmall` |
| 6 | Row count in `meas_badStep_le`, `meas_badTower_le` | `#Idx = size n = (WL)^d` (RBM2D `(WL)²`); `d=3,L=3,W=2`: `216` | per letter factor `(ε + size)/ε` | only `d`-dependence of the file besides the type `Idx d …` (grep: `W ^ 2`, `Z2`, scales, weights, `lam`, `∀ᶠ`: 0 hits in lines 1-912; `(W L)²` only in 2 docstrings) |
| 7 | `hsmall: condEnv^K · P(badTower(M+1)) ≤ B₀^K (2Ψ)^{KM}`, `B₀ = B/2` | with `meas_badTower_le`, `meas_badBase`: suffices `P(Ω^c) ≤ W^{-D}`, `D ≥ D_W := log_W[condEnv^K((ε+size)/ε)^{M+1}/(B₀^K(2Ψ)^{KM})]` | `D_∞ = (M+1)(2d + c(M+1)) + cK(M+1)`; `L = W`, `c=1`, `M=1`, `K=2`, `d=3`: `20` (in `N=(WL)^d`: `N^{-20/6}`) | `P(Ω^c) ≤ W^{-D}` for every `D` is `‖G_t − M‖_max ≺ W^{-ε₀}` of `initialGT2` (`3_5:28-29`; `≺` = bound with probability `≥ 1 − W^{-D}` for all `D`); `D_W < 20` (limit below); external premise (G4.12), stays a hypothesis |
| 8 | Envelope `‖applyOps L (Δ_{qList L} Z_k)(ω)‖ ≤ condEnv E t M`, `|L| ≤ M` (MinorDiffCond:518) | `t=1/2`: `condEnv(M=q) = 6, 24, 96` for `q = 0,1,2` | pointwise for every `ω` | measured max over 10^3 samples (iii): `0.55, 0.15, 0.043` (W=2): slack `≥ 10, 160, 2200` |
| 9 | §29 (1) time domain | `u : ℝ` arbitrary in `norm_…_condEnv`, `integral_prod_…_le_on`, `…_le_badFamily` (D210); endpoint takes `u = t n` | `|E n| < 2`, `t n < 1` only; `0 ≤ t n` never used (η > 0 for every `t<1`; `u<0` gives `√u = 0`, `H=0`, still true) | none |
| 10 | §29 (2),(3),(4) | no `ilambda`, no window, no `L^d ≤ W^K` in any statement (`L^d ≤ W^K` appears only in the asymptotic check of row 7, where `L = W`); statements at one slice `n` (`hE: |E n|<2`), no `∀ n`, no `∀ᶠ n` | `∀ᶠ n` is the consumer's: `hB1`, `hδ4`, `hMδ`, `hsmall` hold eventually (rows 4, 7) | none |
| 11 | §30 / D192 weights | 0 occurrences of `UniformWeight`, `BoundedWeight`, `svar`, `lam` in the source (`grep -c` = 0); no mass bound `c·#A ≤ 1` | not applicable | none |
| 12 | MD-layer imports (`Path/Step2Props`) | the source uses `etaT`, `etaT_pos`, `llErrMat`, `spectralZ/M`; merged: `RBM.Gauss.etaT`, `etaT_pos` (`Loop/GLoop:75,83`), `llErrMat d L W …` (`Green/Pins:73`, explicit `d L W`), `zt`, `mE`; bridge from `llErrMat ≤ δ` to `GoodEvent (green H z) m δ`: `Gres = Ring.inverse` vs `green = Matrix.inv`, same as `FlucVanish:683` | no ST-2 import | none |
| 13 | Registry `RBM.Green.MinorDiffGainUpTo'` (`Test/Axioms.lean:190`; ticket says 191) | stays: still a hypothesis of merged `flucGainUpTo'_of_minorDiffGainUpTo'`; the endpoint proves it only under `hB1`, `hsmall` (owed high-probability input, G4.12) | line cannot go; its comment "proved by S1-25" is wrong (S1-25 gives the word estimate; `:869` is S1-26, conditional) — comment fix is a dispatcher edit (append-only rule) | `BadFamily` (a `Prop` structure, produced by `badFamily_badTower`): predicted structural; to be fixed by the registry pre-check in 1b |

### (ii) One concrete nondegenerate instance

`d = 3`, `L = 3`, `W = 2`, `size = 216`, `E = 0`, `t = u = 0`, `M = 1`, `K = 2`, `δ = 2^{-20}`, `ε = condEps = 2^{-42}`. Command `python3 inst.py`:
```
minorDiffC(M), M=0,1,2: 8 131072 2^91 ; atomC(1)= 32
d=3 L=3 W=2 size=(WL)^d=216  E=0 t=0 eta=1 |E|<2:True t<1:True
M=1 K=2 delta=2^-20 Psi=2delta eps=condEps=1/4398046511104 (=2^-42:True)  condEnv=16  condCost=1/524288 (=Psi:True)
hdelta0: 0<delta True;  hdelta4: delta<=1/4 True;  hMdelta: 8*M*delta<=1 True;  hdelta eps>=0 True
B0=2*C_M*Psi+condCost=262145/524288=0.5000019  hB1: B0<=1 True;  B=2*B0=262145/262144=1.0000038;  rho=2*Psi=1/262144=3.815e-06  rho<1:True
hsmall: LHS=condEnv^K * P.real(badTower(M+1)); at t=0, H_0=0, G=(0-z)^-1=m, llErrMat=0<=delta for every omega: good set = whole space, badBase null, tower null; RHS=B0^K*(2Psi)^(K*M)= 3.638006562720268e-12 >=0
  layer q=0: B*rho^q = 1.0000e+00
  layer q=1: B*rho^q = 3.8147e-06
t=0 numeric: N=216, H_0=0, max_ij |G_ij - m 1_{i=j}| = 0.0e+00 <= delta=9.54e-07: True
```
At `t = 0`: `H_0 = 0` (`√0 = 0`), `G = (0 − z)⁻¹ = m·1`, so `{‖G−m‖_max ≤ δ}` is the whole space, `badBase` is null, every `badTower` is null: `hsmall` is `0 ≤ RHS`. The conclusion is not trivial as a statement (`B ≈ 1.0000038 > 0`, `ρ = 2^{-18}`, all `ι` with `#ι ≤ 2`, all words of length `≤ 1`); the probabilistic content of `hsmall` at `t > 0` is the external premise, checked as a limit. Not `N = 0`, empty index, or collapsed window; `δ` is not astronomically small (`2^{-20}`, forced by `C_1 = 2^17`, row 4). At `M = 2`, `hB1` forces `δ ≲ 2^{-92}` (row 4); the instance uses `M = 1`.

External hypothesis `hsmall` (TEAM §8 lesson 14), `d = 3`, `L = W`, `c = 1`, `M = 1`, `K = 2`, `E = 0`, `t = 1/2`, `δ = W^{-c}`. `python3 limit.py`:
```
condEnv(E=0,t=1/2,M=1)= 24 ; hB1 threshold: (2C_1+1)*2*W^-c<=1 <=> W>= 524290
W=1e6: size=(WL)^d=1e36; hB1:True 8M*delta<=1:True; D_W=log_W(needed/P-scale)=18.612
W=1e9: size=(WL)^d=1e54; hB1:True 8M*delta<=1:True; D_W=log_W(needed/P-scale)=19.075
W=1e12: size=(WL)^d=1e72; hB1:True 8M*delta<=1:True; D_W=log_W(needed/P-scale)=19.306
W=1e18: size=(WL)^d=1e108; hB1:True 8M*delta<=1:True; D_W=log_W(needed/P-scale)=19.537
W=1e30: size=(WL)^d=1e180; hB1:True 8M*delta<=1:True; D_W=log_W(needed/P-scale)=19.722
limit D_inf = (M+1)(2d + c(M+1)) + c K (M+1) = 20
```
`D_W` increases to `20` from below; `hB1`, `hMδ` hold from `W = 524290`. So `hsmall` holds eventually in `n` from `P(Ω^c) ≤ N^{-D}` with `D` large (fixed by `M, K, c, d`); `ε⁻¹` and `condEnv^K` are polynomial in `W` for `1 − t` polynomially bounded below.

Numeric check (iii), `d = 3`, `L = 3`, `g = 1/2`, `E = 0`, `u = t = 1/2` (`z = i/2`, `η = 1/2`), `W = 2, 3, 4`, `10^3` samples each, `k = 0`, `κ_1`, `κ_2` in the block of `k`. `X_q = Q_{κ_1}⋯Q_{κ_q} Q_k Δ_{κ_1}⋯Δ_{κ_q}(G^{(·)}_{kk} − m)` (`= applyOps L (Δ_{qList L} Z_k)` by `minorDiff_flucDiagSet_eq`, `applyOps_append`); `E_{T'}` = integral over fresh entries of all rows in `T'` (coordinate `(i,j)` is in row `k` iff `i = k ∨ j = k`), 200 inner draws, evaluated by Schur complement onto `T = {k,κ_1,κ_2}`. Schur block checked against direct inversion of the resampled `N×N` matrix, and `ΔΔ` against direct minors (`python3 env.py check`; `python3 ycheck.py`): max err `1.1e-15`, `q=2`: equal to 12 digits. Command `python3 env.py 100 200 2,3,4` (2558 s CPU):
```
d=3 L=3 g=0.5 E=0.0 u=t=0.5 eta=0.5 nin=200 samples/W=1000; condEnv(q)=2^(2q+1)(1/eta+1) = {0: 6.0, 1: 24.0, 2: 96.0}
W=2 N=216 q=0 samples=1000 rms|X|=1.8464e-01 mean|X|=1.6351e-01 q99=3.8637e-01 max|X|=5.5115e-01 condEnv=6.0 max<=condEnv:True  rms*W^((q+1)d/2)=0.522  [3s]
W=2 N=216 q=1 samples=1000 rms|X|=3.4312e-02 mean|X|=2.8571e-02 q99=1.0145e-01 max|X|=1.4884e-01 condEnv=24.0 max<=condEnv:True  rms*W^((q+1)d/2)=0.274  [3s]
W=2 N=216 q=2 samples=1000 rms|X|=8.8671e-03 mean|X|=7.0484e-03 q99=2.5000e-02 max|X|=4.3177e-02 condEnv=96.0 max<=condEnv:True  rms*W^((q+1)d/2)=0.201  [3s]
W=3 N=729 q=0 samples=1000 rms|X|=1.0355e-01 mean|X|=9.0866e-02 q99=2.4314e-01 max|X|=2.7921e-01 condEnv=6.0 max<=condEnv:True  rms*W^((q+1)d/2)=0.538  [33s]
W=3 N=729 q=1 samples=1000 rms|X|=1.0600e-02 mean|X|=8.2656e-03 q99=3.5236e-02 max|X|=6.7066e-02 condEnv=24.0 max<=condEnv:True  rms*W^((q+1)d/2)=0.286  [33s]
W=3 N=729 q=2 samples=1000 rms|X|=1.5317e-03 mean|X|=1.1328e-03 q99=5.3131e-03 max|X|=9.6595e-03 condEnv=96.0 max<=condEnv:True  rms*W^((q+1)d/2)=0.215  [33s]
W=4 N=1728 q=0 samples=1000 rms|X|=6.5539e-02 mean|X|=5.7190e-02 q99=1.4995e-01 max|X|=2.0101e-01 condEnv=6.0 max<=condEnv:True  rms*W^((q+1)d/2)=0.524  [303s]
W=4 N=1728 q=1 samples=1000 rms|X|=4.4238e-03 mean|X|=3.5579e-03 q99=1.4379e-02 max|X|=2.2046e-02 condEnv=24.0 max<=condEnv:True  rms*W^((q+1)d/2)=0.283  [303s]
W=4 N=1728 q=2 samples=1000 rms|X|=4.2219e-04 mean|X|=3.1313e-04 q99=1.2997e-03 max|X|=2.5720e-03 condEnv=96.0 max<=condEnv:True  rms*W^((q+1)d/2)=0.216  [303s]
log-slope rms|X_q| W=2->4: q=0: -1.494  (predicted -(q+1)d/2 = -1.5)
log-slope rms|X_q| W=2->4: q=1: -2.955  (predicted -(q+1)d/2 = -3.0)
log-slope rms|X_q| W=2->4: q=2: -4.393  (predicted -(q+1)d/2 = -4.5)
per-layer exponent (slope_q - slope_(q-1)) = -1.461 (predicted -d/2 = -1.5)
per-layer exponent (slope_q - slope_(q-1)) = -1.437 (predicted -d/2 = -1.5)
```
(`rms*W^{(q+1)d/2}` is the constant in front of `W^{-(q+1)d/2}`: `0.52, 0.27–0.29, 0.20–0.22` for `q = 0,1,2` at all three `W`; the inner Monte-Carlo noise inflates `rms` slightly.) Envelope never exceeded; per-layer exponent of `W` is `d/2 = 1.5` (measured `1.46`, `1.44`).

### Verdict per target
- `minorDiffGainUpTo'_goodEvent` (:869), `flucGainUpTo'_goodEvent` (:890): **PASS**. Hypotheses `|E n| < 2`, `t n < 1`, `ε ≥ 0`, `0 < δ ≤ 1/4`, `8Mδ ≤ 1`, `hB1`, `hsmall` hold at the (ii) instance; `B`, `ρ < 1` and the layer exponents are `d/2` for every `q ≤ 2` (row 2); statement unchanged at `d ≥ 3` (the `d`-dependence is the row count, row 6). `hsmall` and `hB1` stay hypotheses (rows 4, 7).
- `badStep`, `badTower`, `BadFamily`, `meas_badStep_le`, `meas_badTower_le`, `norm_applyOps_le_badFamily`, `condEnv`, `condCost`, `norm_applyOps_minorDiff_flucDiagSet_le_condEnv`, `integral_prod_applyOps_minorDiff_le_on`, `badBase`: **PASS** (measure-theoretic or arithmetic, `d`-free except `size = (WL)^d`; envelope checked numerically, row 8). Every other public declaration of lines 1-912 is dimension-free and is ported (none dropped).

## (a′) Preflight corrections — Sun Oct  4 06:54:59 UTC 2026
Row 13 of (a) predicted that `RBM.Green.MinorDiffGainUpTo'` "cannot go" and that `BadFamily` is structural. The registry pre-check (b.8) shows: (1) the scan does not report `BadFamily` (`badFamily_badTower` concludes it): no line to append; (2) with this file imported the scan no longer reports `MinorDiffGainUpTo'` (premises found 83 -> 82, the line moves to "carry nothing yet", exit 0), because `minorDiffGainUpTo'_goodEvent` concludes it. `hsmall` is a measure inequality, not a `Prop`-valued predicate, so the scan does not see the debt that remains there. Also: the ported declarations are lines 98-903 of the source (b.6), not 1-912. No verdict changes.

**Correction (Sun Oct  4 07:10:45 UTC 2026; audit round 1, §4a).** (ii) says "The conclusion is not trivial as a statement": false. At `t = 0`, `H_0 = 0` and `G^(S)_kk − m ≡ 0`, so every left side at the (ii) instance is `0` and the conclusion reduces to `0 ≤ B^#ι ρ^Σq`. The instance at a positive time is in (b.4).

## (b) Script output — Sun Oct  4 06:54:59 UTC 2026
Branch `t/T2117`, commits `be89bd6`, repair `890acb7` (base `975f4ff`). `git diff --stat main...HEAD | tail -1`: ` 1 file changed, 1418 insertions(+)` (`RBM3D/Green/MinorDiffCond.lean` only).
**b.1 Build** (repair commit `890acb7`, Sun Oct  4 07:10:45 UTC 2026; `date -u` before the build: Sun Oct  4 07:09:59 UTC 2026). `lake build RBM3D.Green.MinorDiffCond 2>&1 | tail -1`; `lake env lean RBM3D/Green/MinorDiffCond.lean; echo exit=$?`; after `touch`, the only warning of the file is the pre-existing long line `MinorDiffCond.lean:81` (header docstring):
```
Build completed successfully (3341 jobs).
exit=0
sorry/admit/native_decide: 0, axiom decls: 0
```
**b.2 Axioms.** `lake env lean axall.lean` with one `#print axioms` per public declaration of the file (54: 38 in `RBM.Green`, 16 `inst_*` in `RBM.Green.MinorDiffCondInst`); summary by script, then the targets verbatim:
```
53 declarations: [propext, Classical.choice, Quot.sound]; 1 declaration: [propext] (numQ_append_true); other axioms: none
'RBM.Green.numQ_append_true' depends on axioms: [propext]
'RBM.Green.minorDiffGainUpTo'_goodEvent' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.flucGainUpTo'_goodEvent' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.MinorDiffCondInst.inst_minorDiffGain' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.MinorDiffCondInst.inst_flucGain' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Repair (`890acb7`): `rep/ax.lean` = `#print axioms` of the 3 word/moment targets, the 2 endpoints and the 8 new `inst_*`; `lake env lean rep/ax.lean` (exit 0), lines joined, then `grep -c` / `grep -vc "[propext, Classical.choice, Quot.sound]"`: `13` / `0`. Excerpt:
```
'RBM.Green.MinorDiffCondInst.inst_minorDiffGain_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.MinorDiffCondInst.inst_flucGain_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.MinorDiffCondInst.inst_integral_prod_half' depends on axioms: [propext, Classical.choice, Quot.sound]
```
**b.3 Target statements** (extracted by `extract.py` from the file; docstrings dropped, whitespace joined, `L<n>` = file line):
```
L111: def badStep (sz : Sizes d) (n : ℕ) (ε : ℝ) (S : Set (Sizes.SeqΩ sz)) : Set (Sizes.SeqΩ sz) := S ∪ ⋃ κ : Idx d (sz.L n) (sz.W n), {ω | ε < (Sizes.seqP sz).real (rowSlice
    sz n κ S ω)}
L137: def badTower (sz : Sizes d) (n : ℕ) (ε : ℝ) (S : Set (Sizes.SeqΩ sz)) : ℕ → Set (Sizes.SeqΩ sz) | 0 => S | j + 1 => badStep sz n ε (badTower sz n ε S j)
L154: structure BadFamily (sz : Sizes d) (n : ℕ) (ε : ℝ) (Bad : ℕ → Set (Sizes.SeqΩ sz)) : Prop where meas : ∀ j, MeasurableSet (Bad j) mono : ∀ j, Bad j ⊆ Bad (j + 1) slice :
    ∀ (j : ℕ) (κ : Idx d (sz.L n) (sz.W n)) {ω : Sizes.SeqΩ sz}, ω ∉ Bad (j + 1) → (Sizes.seqP sz).real (rowSlice sz n κ (Bad j) ω) ≤ ε
L190: theorem meas_badStep_le (sz : Sizes d) (n : ℕ) {ε : ℝ} {S : Set (Sizes.SeqΩ sz)} (hS : MeasurableSet S) : ENNReal.ofReal ε * (Sizes.seqP sz) (badStep sz n ε S) ≤
    (ENNReal.ofReal ε + (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ≥0∞)) * (Sizes.seqP sz) S
L231: theorem meas_badTower_le (sz : Sizes d) (n : ℕ) {ε : ℝ} {S : Set (Sizes.SeqΩ sz)} (hS : MeasurableSet S) (j : ℕ) : ENNReal.ofReal ε ^ j * (Sizes.seqP sz) (badTower sz n ε
    S j) ≤ (ENNReal.ofReal ε + (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ≥0∞)) ^ j * (Sizes.seqP sz) S
L301: theorem norm_applyOps_le_badFamily {X : Sizes.SeqΩ sz → ℂ} (hX : BddMeas sz X) {Bad : ℕ → Set (Sizes.SeqΩ sz)} {ε Env c : ℝ} (hfam : BadFamily sz n ε Bad) (hEnv : ∀ ω, ‖X
    ω‖ ≤ Env) (hc : 0 ≤ c) (hε : 0 ≤ ε) (hgood : ∀ ω ∉ Bad 0, ‖X ω‖ ≤ c) : ∀ (l : List (Bool × Idx d (sz.L n) (sz.W n))) (ω : Sizes.SeqΩ sz), ω ∉ Bad l.length → ‖applyOps
    sz n l X ω‖ ≤ 2 ^ numQ l * (c + l.length * Env * ε)
L504: noncomputable def condEnv (E t : ℝ) (M : ℕ) : ℝ := 2 ^ (2 * M + 1) * ((etaT E t)⁻¹ + 1)
L516: noncomputable def condCost (E t : ℝ) (M : ℕ) (Ψ ε : ℝ) : ℝ := ((M : ℝ) + 1) * condEnv E t M * ε * ((2 * Ψ) ^ M)⁻¹
L527: theorem norm_applyOps_minorDiff_flucDiagSet_le_condEnv (hE : |E| < 2) (ht : t < 1) (u : ℝ) {M : ℕ} (k : Idx d (sz.L n) (sz.W n)) (L : List (Bool × Idx d (sz.L n) (sz.W
    n))) (hM : (L).length ≤ M) (ω : Sizes.SeqΩ sz) : ‖applyOps sz n L (minorDiff sz n (qList L) (flucDiagSet sz n u (zt E t) (mE E) k)) ω‖ ≤ condEnv E t M
L566: theorem integral_prod_applyOps_minorDiff_le_on (hE : |E| < 2) (ht : t < 1) (u : ℝ) {Ψ ε : ℝ} (hΨ0 : 0 < Ψ) (hΨhalf : 2 * Ψ ≤ 1) (hε : 0 ≤ ε) {M : ℕ} {Bad : ℕ → Set
    (Sizes.SeqΩ sz)} (hfam : BadFamily sz n ε Bad) (hgood : ∀ ω ∉ Bad 0, MinorGoodLe sz n u (zt E t) (mE E) ω Ψ M) (ι : Type) [Fintype ι] (k : ι → Idx d (sz.L n) (sz.W
    n)) (L : ι → List (Bool × Idx d (sz.L n) (sz.W n))) (h1 : ∀ i, ((L i).map Prod.snd).Nodup) (h2 : ∀ i, ∀ x ∈ L i, x.2 ≠ k i) (hM : ∀ i, (L i).length ≤ M) : ∫ ω, ∏ i,
    ‖applyOps sz n (L i) (minorDiff sz n (qList (L i)) (flucDiagSet sz n u (zt E t) (mE E) (k i))) ω‖ ∂(Sizes.seqP sz) ≤ (2 * minorDiffC M * Ψ + condCost E t M Ψ ε) ^
    Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i) + condEnv E t M ^ Fintype.card ι * (Sizes.seqP sz).real (Bad (M + 1))
L706: noncomputable def badBase (sz : Sizes d) (E t δ : ℕ → ℝ) (n : ℕ) : Set (Sizes.SeqΩ sz) := toMeasurable (Sizes.seqP sz) {ω : Sizes.SeqΩ sz | ∀ i j : Idx d (sz.L n) (sz.W
    n), llErrMat d (sz.L n) (sz.W n) (E n) (t n) (Sizes.seqHflow sz n (t n) ω) i j ≤ δ n}ᶜ
L888: theorem minorDiffGainUpTo'_goodEvent (hE : |E n| < 2) (ht1 : t n < 1) {ε : ℝ} (hε : 0 ≤ ε) {M K : ℕ} (hδ0 : 0 < δ n) (hδ4 : δ n ≤ 1 / 4) (hMδ : 8 * M * δ n ≤ 1) (hB1 : 2
    * minorDiffC M * (2 * δ n) + condCost (E n) (t n) M (2 * δ n) ε ≤ 1) (hsmall : condEnv (E n) (t n) M ^ K * (Sizes.seqP sz).real (badTower sz n ε (badBase sz E t δ n)
    (M + 1)) ≤ (2 * minorDiffC M * (2 * δ n) + condCost (E n) (t n) M (2 * δ n) ε) ^ K * (2 * (2 * δ n)) ^ (K * M)) : MinorDiffGainUpTo' sz n (t n) (zt (E n) (t n)) (mE
    (E n)) (2 * (2 * minorDiffC M * (2 * δ n) + condCost (E n) (t n) M (2 * δ n) ε)) (2 * (2 * δ n)) M K
L909: theorem flucGainUpTo'_goodEvent (hE : |E n| < 2) (ht1 : t n < 1) {ε : ℝ} (hε : 0 ≤ ε) {M K : ℕ} (hδ0 : 0 < δ n) (hδ4 : δ n ≤ 1 / 4) (hMδ : 8 * M * δ n ≤ 1) (hB1 : 2 *
    minorDiffC M * (2 * δ n) + condCost (E n) (t n) M (2 * δ n) ε ≤ 1) (hsmall : condEnv (E n) (t n) M ^ K * (Sizes.seqP sz).real (badTower sz n ε (badBase sz E t δ n) (M
    + 1)) ≤ (2 * minorDiffC M * (2 * δ n) + condCost (E n) (t n) M (2 * δ n) ε) ^ K * (2 * (2 * δ n)) ^ (K * M)) : FlucGainUpTo' sz n (t n) (zt (E n) (t n)) (mE (E n)) (2
    * (2 * minorDiffC M * (2 * δ n) + condCost (E n) (t n) M (2 * δ n) ε)) (2 * (2 * δ n)) M K
```
**b.4 Compiled nonempty instances** (repair `890acb7`; `szC`: `d = 3`, `L = 3`, `W = 2`, `lam = 1/2`, `n = 0`, `size 0 = 216`, `inst_size`). Statements extracted by `bash rep/ext.sh <names>` (from `theorem <name>` to the first line ending in `:=`/`:= by`):
```
L1359: theorem inst_minorDiffGain_pos
    (hsmall : condEnv 0 (1 / 100000000) 0 ^ 2 * (Sizes.seqP szC).real
        (badTower szC 0 (condEps 0 (1 / 100000000) 0 (2 * (1 / 64 : ℝ)))
          (badBase szC (fun _ => 0) (fun _ => 1 / 100000000) (fun _ => 1 / 64) 0) (0 + 1))
      ≤ (2 * minorDiffC 0 * (2 * (1 / 64 : ℝ))
          + condCost 0 (1 / 100000000) 0 (2 * (1 / 64 : ℝ))
              (condEps 0 (1 / 100000000) 0 (2 * (1 / 64 : ℝ)))) ^ 2
        * (2 * (2 * (1 / 64 : ℝ))) ^ (2 * 0)) :
    MinorDiffGainUpTo' szC 0 (1 / 100000000) (zt 0 (1 / 100000000)) (mE 0) (17 / 16)
      (2 * (2 * (1 / 64 : ℝ))) 0 2 := by
L1265: theorem inst_envelope_half (ω : Sizes.SeqΩ szC) :
    ‖applyOps szC 0 ([(true, siteB), (false, siteC)] : List (Bool × Idx 3 (szC.L 0) (szC.W 0)))
        (minorDiff szC 0
          (qList ([(true, siteB), (false, siteC)] : List (Bool × Idx 3 (szC.L 0) (szC.W 0))))
          (flucDiagSet szC 0 (1 / 2) (zt 0 (1 / 2)) (mE 0) siteA)) ω‖
      ≤ 96 := by
L1287: theorem inst_norm_applyOps_le_badFamily_half (ω : Sizes.SeqΩ szC)
    (hω : ω ∉ badTower szC 0 1 halfS 2) :
    ‖applyOps szC 0 ([(true, siteB), (false, siteC)] : List (Bool × Idx 3 (szC.L 0) (szC.W 0)))
        (flucDiagSet szC 0 (1 / 2) (zt 0 (1 / 2)) (mE 0) siteA ∅) ω‖
      ≤ 2 ^ numQ ([(true, siteB), (false, siteC)] : List (Bool × Idx 3 (szC.L 0) (szC.W 0)))
          * (6 + (([(true, siteB), (false, siteC)] :
              List (Bool × Idx 3 (szC.L 0) (szC.W 0))).length : ℝ) * 6 * 1) :=
L1304: theorem inst_integral_prod_half :
    ∫ ω, ∏ _i : Fin 1, ‖applyOps szC 0 [(true, siteB)]
        (minorDiff szC 0 (qList [(true, siteB)])
          (flucDiagSet szC 0 (1 / 2) (zt 0 (1 / 2)) (mE 0) siteA)) ω‖ ∂(Sizes.seqP szC)
      ≤ (2 * minorDiffC 1 * (1 / 8) + condCost 0 (1 / 2) 1 (1 / 8) (condEps 0 (1 / 2) 1 (1 / 8)))
            ^ Fintype.card (Fin 1) * (2 * (1 / 8)) ^ ∑ _i : Fin 1, numQ [(true, siteB)]
        + condEnv 0 (1 / 2) 1 ^ Fintype.card (Fin 1) * (Sizes.seqP szC).real
            (badTower szC 0 (condEps 0 (1 / 2) 1 (1 / 8))
              (badBase szC (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 1 / 16) 0)
              (1 + 1)) := by
```
- **Endpoints at `t = 10^-8 > 0`** (`inst_minorDiffGain_pos`, `inst_flucGain_pos` (same hypothesis, conclusion `FlucGainUpTo'`), `inst_gain_applied_pos` (applied at `ι = Fin 2`, rows `(0,0,0)`, `(0,0,1)`, empty words)): `E = 0`, `M = 0`, `K = 2`, `δ = 1/64`, `ε = condEps`; `|0| < 2`, `t < 1`, `hε`, `hδ0`, `hδ4`, `hMδ`, `hB1` (`inst_pos_hB1`: `17/32 ≤ 1`) are discharged; `(B, ρ) = (17/16, 1/16)`. `hsmall` is a hypothesis (owed input, G4.12); it is true at these data by the chain below (union bound on the entries, `‖X‖ ≤` max row `ℓ¹`, `‖G − m‖_max ≤ t/(1−t) + √t‖X‖/(1−t)²` at `z = (1−t)i`, `m = i`, then `meas_badTower_le` at `j = M+1 = 1`). `python3 rep/hsmall_rep.py` (section (B) is used in (d) T2117c):
```
N=216 rowsum(S)=1.000000..1.000000 Smax=0.05 offdiag pairs with S>0: 5940
== (A) endpoint instance: E=0 t=1e-8 M=0 K=2 delta=1/64 Psi=1/32 eps=condEps ==
condEnv=4.0000000200 eps=7.812500e-03 condCost=Psi:True B0=17/32 hB1(B0<=1):True B=2B0=17/16 rho=2Psi=1/16
hdelta0:True hdelta4:True hMdelta:True t<1:True
union bound (cth=45): P(some |X_ij|>sqrt(45 S_ij)) <= 3.654e-08; on complement ||X||_op <= 48.0000; max|G-m| <= 4.800010e-03 <= delta=1.562500e-02: True
P(badBase) <= 3.654e-08; meas_badTower_le (j=M+1=1): P(T1) <= (1+N/eps) P(badBase) = 1.010e-03
hsmall: LHS = condEnv^K P(T1) <= 1.617e-02   RHS = B0^K (2Psi)^(KM) = 0.282227   holds: True
MC 1000 samples t=1e-8: max ||X||_op=2.2348 (bound 48.00); max_samples max_ij|G-m1|=1.084e-04; frac(>delta)=0.0
== (B) M=1 (T2117c): hB1 => 2*C_1*2*delta<=1 => delta<=2^-19; hsmall (K>=1, B0<=1, condEnv>=16) => P(maxerr>delta)<=(4delta/16)^K ==
W=2 t=1e-09: 200 samples median max|G-m|=2.122e-05 frac(>2^-19)=1.000
W=2 t=1e-10: 200 samples median max|G-m|=6.711e-06 frac(>2^-19)=1.000
W=2 t=1e-11: 200 samples median max|G-m|=2.122e-06 frac(>2^-19)=0.915
W=2 t=1e-12: 200 samples median max|G-m|=6.711e-07 frac(>2^-19)=0.000
W=2 t=1e-13: 200 samples median max|G-m|=2.122e-07 frac(>2^-19)=0.000
sufficient chain cth=45.0: P(bad X)<=3.65e-08, R=48.00, max|G-m|<=2^-19 for t<=1.58e-15
sufficient chain cth=220.0: P(bad X)<=3.65e-46, R=106.13, max|G-m|<=2^-19 for t<=3.23e-16
```
- **`u = t = 1/2`** (`inst_envelope_half`, `inst_norm_applyOps_le_badFamily_half`, `inst_integral_prod_half`): every hypothesis discharged (`hEnv`, `hgood` with `Env = c = 6` from `norm_flucDiagSet_le_env`, `zt_half_im : Im z = 1/2`; `hgood` of the moment bound from `minorGoodLe_of_notMem_badBase` at `δ = 1/16`, `M = 1`; `inst_condEnv_half : condEnv 0 (1/2) 2 = 96`). For the `badFamily` instance, `0 ∉ badTower 1 halfS 2` (`zero_notMem_tower`), so the premise set is nonempty.
- **Collapsed (`t = u = 0`):** `inst_minorDiffGain`, `inst_flucGain`, `inst_gain_applied`, `inst_envelope`, `inst_norm_applyOps_le_badFamily` and the `integral_prod_…` `example`: at `t = 0` the integrand/left side is `≡ 0` (audit §4a); their docstrings now say so. They are kept as checks that the hypotheses discharge jointly at `t = 0` (`hsmall` proved, `inst_hsmall`).
- Other instances (unchanged): `inst_meas_badStep`, `inst_meas_badTower`, `inst_meas_badTower_size` (half-space `S = {ω | ω_c < 0}`, `ε = 1`, 216 rows), `inst_badFamily`, `inst_badBase_null`, `inst_condEnv`, `inst_condEps`, `inst_condCost`, `inst_minorDiffC_one`. The `t = 1/2` example of `minorDiffGainUpTo'_goodEvent` with a false `hsmall` (audit §4b) is removed.

**b.5 Name clash.** `bash clash.sh` (`git grep -nE "^(@\[..\] )?(noncomputable )?(private )?(theorem|def|lemma|structure|abbrev|inductive|instance) ([A-Za-z_.]*\.)?<name>( |$|:)" main -- RBM3D`, excluding this file, for each of the 54 public names):
```
checked 54 public names against main (2270c89): 0 clashes
```
Repair names (`inst_condEnv_half inst_envelope_half inst_norm_applyOps_le_badFamily_half inst_integral_prod_half inst_minorDiffC_zero inst_minorDiffGain_pos inst_flucGain_pos inst_gain_applied_pos`): `for n in …; do git grep -nE "(theorem|def|lemma) ([A-Za-z_.]*\.)?$n( |$|:)" main -- RBM3D | wc -l; done | tr '\n' ' '`: `0 0 0 0 0 0 0 0`.
**b.6 Port.** Source `../RBM2D/RBM2D/Green/MinorDiffCond.lean` at `c9a24cf` (read by `git show`; `git -C ../RBM2D log -1` = `9e0f275`). Ported lines 98-903 (806 lines); the header docstring (1-97) is rewritten; `section Checks` (905-1387) is replaced by the instances of b.4. Source lines `name:line` of the key declarations:
```
badStep:102, badTower:128, BadFamily:145, BadFamily.mono_le:154, meas_badStep_le:181, meas_badTower_le:222, norm_applyOps_le_badFamily:292,
condEnv:495, condCost:507, norm_applyOps_minorDiff_flucDiagSet_le_condEnv:518, integral_prod_applyOps_minorDiff_le_on:557, badBase:691,
minorDiffGainUpTo'_of_le_on:792, minorDiffGainUpTo'_goodEvent:869, flucGainUpTo'_goodEvent:890
```
Rename script `port.py` (R1, R2, R3 of ST1-COMMON item 2, plus `spectralZ/M -> zt/mE`, `RBM.Path.etaT -> etaT`, `llErrMat (d.L n) (d.W n) -> llErrMat d (sz.L n) (sz.W n)`, remaining token `d -> sz`) applied to source lines 98-903, then `diff` against the file (lines 106-921), i.e. **every residual difference**:
```
$ diff body.lean filebody.lean
83c83
< the `size n = (W L)²` sites of the lattice (`flucAvg_card_Idx_eq_size`); RBM1D has `N`. -/
---
> the `size n = (W L)^d` sites of the lattice (`flucAvg_card_Idx_eq_size`); RBM1D has `N`. -/
584a585,590
> 
> /-- The merged `Gres H z true` (a `Ring.inverse`) is `RBM.green H z = (H - z)⁻¹` (the private lemma
> `flucIterHigh_Gres_true_eq_green` of `Green/MinorGoodLe.lean`, restated). -/
> private theorem minorDiffCond_Gres_true {ι : Type*} [Fintype ι] [DecidableEq ι]
>     (H : Matrix ι ι ℂ) (z : ℂ) : Gres H z true = green H z := by
>   simp only [green, Gres, ↓reduceIte, Matrix.nonsing_inv_eq_ringInverse]
621c627,631
<   exact minorGoodLe_of_goodEvent_flow hE hz hδ0 hδ4 hMδ hmem
---
>   have hG : GoodEvent (green (Sizes.seqHflow sz n (t n) ω) (zt (E n) (t n))) (mE (E n)) (δ n) := by
>     intro i j
>     have h := hmem i j
>     simpa only [llErrMat, minorDiffCond_Gres_true] using h
>   exact minorGoodLe_of_goodEvent_flow hE hz hδ0 hδ4 hMδ hG
806c816
< end Endpoints
\ No newline at end of file
---
> end Endpoints
```
`git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Green/MinorDiffCond.lean`: `666 +++---`, `38 insertions(+), 628 deletions(-)`: HEAD has no `section Checks`; a script diff of the `theorem`/`def`/`structure` head lines of source lines 98-903 against HEAD lists two heads present only at `c9a24cf` (`badTower_zero`, `minorDiffCond_meas_badStep_le_size`), and docstrings and some proofs differ (for instance `simp [badTower]` at HEAD); the port follows `c9a24cf` as the ticket says. No RBM1D file is ported (RBM1D is cited only through the source docstrings).
**b.7 `d = 2` tokens** (ST1-COMMON item 2). `sed -n 98,903p src | grep -nE "W ?\^ ?2|Z2|\(W L\)²|\(W \* L\)|inv2|d = 2|1/5|scal|ellT|tailT|ellStar|Meta|ellz|lam|ilambda|∀ᶠ|UniformWeight|BoundedWeight|svar"` gives one hit, a docstring, replaced by `(W L)^d` in the file; the same pattern on the file lines 106-921 (the ported part) gives 0 hits (`| wc -l` = 0). In the whole source the string `d = 2` occurs once (`grep -c` = 1, line 64: the heading `## d = 2 and differences from RBM1D` of the header docstring, not ported); portmap row 56 lists `d=2:1`. The only `d`-dependence of the ported lines is the type `Idx d (sz.L n) (sz.W n)` and the row count `size n = (W L)^d`. The hit (line number relative to line 98, i.e. source line 180):
```
83:the `size n = (W L)²` sites of the lattice (`flucAvg_card_Idx_eq_size`); RBM1D has `N`. -/
```
**b.8 Registry pre-check** (ST1-COMMON item 8). Scratch files outside the repository: `precheck.lean` = `import RBM3D`, `import RBM3D.Green.MinorDiffCond`, `#assert_rbm_axioms`; `precheck0.lean` = the same without the second import. `lake env lean precheck.lean` exit 0 (and `precheck0.lean` exit 0). `diff pre_without.out pre_with.out`:
```
1c1
< axiom audit: 3580 theorems, 1253 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
---
> axiom audit: 3630 theorems, 1261 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
111,112c111,112
<   RBM.Green.MinorDiffGainUpTo': 1 [no certificate]
<   RBM.Green.FlucGainUpTo': 3 [no certificate]
---
>   RBM.Green.MinorDiffGainUpTo': 4 [no certificate]
>   RBM.Green.FlucGainUpTo': 5 [no certificate]
115,116c115,116
< premises found by scanning: 83 (borrowed 2, owed 65, structural 16).
< registry: 5 borrowed + 103 owed + 39 structural; 64 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
---
> premises found by scanning: 82 (borrowed 2, owed 64, structural 16).
> registry: 5 borrowed + 103 owed + 39 structural; 65 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
155a156
>  RBM.Green.MinorDiffGainUpTo',
```
`BadFamily` (a `Prop` structure) is not in the scan result; no new `Prop`-valued predicate is introduced. No line was appended to `RBM3D/Test/Axioms.lean`; it is not touched. `MinorDiffGainUpTo'` (line 190) is no longer reported by the scan; the line may go (a removal, so a dispatcher edit), and its comment "proved by S1-25" is wrong: the conditional proof is `minorDiffGainUpTo'_goodEvent` (S1-26).
Repair rerun (`890acb7`): `lake env lean precheck.lean` exit 0; `diff pre_with.out rep/pre_with2.out`: line 1 `3630 -> 3638 theorems`; `MinorDiffGainUpTo': 4 -> 5`, `FlucGainUpTo': 5 -> 6` uses; no other change.
**b.9 Full build** (Sun Oct  4 06:53:50 UTC 2026, at `be89bd6`; not rerun after the repair). `lake build 2>&1 | tail -3`: `Build completed successfully (3861 jobs).` (root `#assert_rbm_axioms` included; the root does not import the new module, the pre-check b.8 does).

**Narrative.**
- The port is the renaming of b.6 plus one private lemma `minorDiffCond_Gres_true` and a 4-line bridge proof in `minorGoodLe_of_notMem_badBase` (`Gres H z true = green H z`, as in the private lemmas of `Green/MinorGoodLe.lean`); no declaration is dropped, no signature is changed beyond the renaming; `MinorDiffGainUpTo'` is the merged definition (`MinorGoodLe.lean:751`), unchanged.
- Gain exponent at `d >= 3`: with `Psi = 2 delta`, `B = 2 (2 C_M Psi + condCost)`, `rho = 2 Psi = 4 delta`; at `eps = condEps`, `condCost = Psi` (`condCost_condEps`), `B = 2 (2 C_M + 1) Psi`. Layer `q <= M` is `B rho^q ∝ delta^(q+1)`; `delta = W^-c` with `c ∈ [eps_0, d/2]`, so each layer gains `W^-c`, sharp `c = d/2` (RBM2D: `W^-1`). (a) measured the per-layer exponent at `d = 3` for `q = 1, 2`: `-1.461`, `-1.437` against `-d/2 = -1.5`, so no layer is steeper than `B rho^q` allows. The statement contains no `W`, `L`, `d` exponent, so it is not false at `d >= 3`; it is the ported statement.
- `hB1` forces `delta <= 1/524290` at `M = 1` (`inst_minorDiffC_one`), so consumers fix `M, K, c` and take `W` large; `hsmall` is the owed input `P(Omega^c) <= W^-D` (G4.12, via `meas_badTower_le`); both stay hypotheses of the endpoints.
- Instances (repair): the endpoints at `t = 10^-8`, `M = 0`, `K = 2`, `δ = 1/64` with every deterministic hypothesis discharged and `hsmall` a hypothesis that is true there (b.4 script); the three word/moment bounds at `u = t = 1/2`, fully discharged. The `t = 0` instances are collapsed (integrand `≡ 0`) and labelled so.
- No ST-2 file is imported (imports: `Green/MinorDiff`, `Green/MinorGoodLe`, `Green/CondDom`); `etaT` is `RBM.Gauss.etaT`, `llErrMat` is `Green/Pins.lean:73`. No weight, no `forall^f n`, no `ilambda`, no window (DECISIONS §29, §30).
- Statements are at one slice `n`; `u` is real in the word and moment bounds (D210), the endpoint takes `u = t n`; `|E n| < 2`, `t n < 1`; `0 <= t n` is not used.

## (c) Verified Mathlib names (`#check` in `mathlib.lean`, all resolved)
`measureReal_le_one`, `measureReal_nonneg`, `MeasureTheory.Measure.real`, `measurableSet_lt`, `measurable_pi_apply`, `measurableSet_toMeasurable`, `subset_toMeasurable`, `measure_toMeasurable`, `Measurable.ennreal_toReal`, `integral_mono`, `integral_add`, `integral_indicator_const`, `integral_const`, `Integrable.norm`, `Finset.prod_le_prod₀`, `Finset.prod_pow_eq_pow_sum`, `Finset.prod_mul_distrib`, `pow_le_pow_of_le_one`, `pow_le_pow_right₀`, `one_le_pow₀`, `measure_iUnion_fintype_le`, `measure_union_le`, `measure_empty`, `measureReal_empty`, `ENNReal.ofReal_le_of_le_toReal`, `ENNReal.toReal_zero`, `Matrix.inv_eq_right_inv`, `Matrix.nonsing_inv_eq_ringInverse`, `Set.mem_iUnion`, `Set.eq_univ_of_forall`, `mul_inv_cancel₀`, `Real.sqrt_sq`, `mul_le_mul_right`, `norm_prod`, `nonpos_iff_eq_zero`. Names verified absent: none searched.

## (d) Open issues and paper-delta candidates
- **T2117a** (Lean construction, no paper counterpart): `badStep`, `badTower`, `BadFamily`, `badBase`, `condEnv`, `condCost`, `condEps`, `minorDiffGainUpTo'_of_le_on` and the constants `minorDiffC M` are Lean's device for passing from the event `Omega(t, eps_0)` (`def_asGMc`, `3_5:16`) to the moment bound; the paper defers the estimate to Lemma 4.1 of `[YY_25]` (`3_5:37`).
- **T2117b** (statement form): the endpoints take the explicit `hB1` and `hsmall` in place of the paper's "`≺`" (probability `>= 1 - W^-D` for all `D`); `hsmall` follows from `P(Omega^c) <= N^-D` with `D >= D_W` (preflight (a) row 7: `D_W -> 20` at `M=1`, `K=2`, `c=1`, `d=3`, `L=W`), the `forall^f n` is the consumer's. Per (a) rows 4 and 7, `hB1` needs `delta <= 1/524290` at `M = 1` (`W >= 524290` at `c = 1`) and `hsmall` needs `D >= D_W`; both hold only eventually in `n` for fixed `M, K, c`.
- **Registry (dispatcher):** `Test/Axioms.lean:190` `RBM.Green.MinorDiffGainUpTo'` now carries nothing in the scan (b.8); remove or retarget it (not an append), correct the comment (S1-25 -> S1-26, conditional on `hsmall`). The debt `hsmall` is not visible to the scan; S1-28 (`FlucThreshold`, consumer of this endpoint) must discharge it from the high-probability local law or carry it as a named hypothesis.
- RBM2D `HEAD` (`9e0f275`) differs from `c9a24cf` in this file (b.6): not compared statement by statement beyond the signature heads.
- **T2117c** (joint satisfiability of `hB1 ∧ hsmall`): for `M ≥ 1`, `hB1` with `ε ≥ 0` forces `2 C_M (2δ) ≤ 1`, i.e. `δ ≤ 2^-19` at `M = 1` (`C_1 = 2^17`) and `δ ≤ 2^-93` at `M = 2`, independently of `W`, `t`, `ε`; for `K ≥ 1`, `0 ≤ t < 1`, `hsmall` (with `B0 ≤ 1`, `condEnv ≥ 16`, `badBase ⊆ badTower`) needs `P(‖G_t − m‖_max > δ) ≤ (δ/4)^K ≤ 2^-21K`. At `W = 2` (b.4 (B)): at every tested `t ≥ 10^-11` the median of `‖G_t − m‖_max` exceeds `2^-19` (`frac ≥ 0.915`), and the sufficient chain holds at `t = 10^-17`, not at `10^-16` (`python3 rep/m1.py`, `M = 1`, `K = 2`, `δ = 2^-20`, `ε = condEps`):
```
M=1 K=2 delta=2^-20 t=1e-17: hB1 B0=0.5000019<=1:True; need P(badBase)<=1.57e-44; cth=220.2 P(bad X)<=3.35e-46<=need:True; R=106.2; max|G-m|<=3.357e-07 <= delta=9.537e-07: True
M=1 K=2 delta=2^-20 t=1e-16: hB1 B0=0.5000019<=1:True; need P(badBase)<=1.57e-44; cth=220.2 P(bad X)<=3.35e-46<=need:True; R=106.2; max|G-m|<=1.062e-06 <= delta=9.537e-07: False
```
  So at `W = 2` no non-extreme data with `M ≥ 1` exist (only `t ≤ 10^-17`-type times); at `t` of order 1 the fluctuation scale `W^-d/2` (preflight (a) row 2) must be `≪ 2^-19`, i.e. `W` large (`W^3/2 ≫ 2^19`; scaling only, not checked numerically). With `M = 0`, non-tiny `δ = 1/64` is admissible (b.4, `t = 10^-8`). This is a consequence of the inherited constants `minorDiffC` (no paper counterpart; the paper has `≺` and unspecified constants).
- Not done: no instance at `M ≥ 1` with `t > 0` (T2117c); no instance at `t > 0` with `hsmall` proved in Lean (needs the local law, G4.12).
