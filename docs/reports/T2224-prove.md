Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 22:58:12 UTC 2026

### (i) Exponent table (no exponent in this ticket: deterministic identities at a fixed size; rows are the thresholds and constants used)

| quantity | value at the instance | constraint (source) | slack |
|---|---|---|---|
| `L` | 4 (`sz0_values`, `Defs/Sizes.lean`) | `3 ≤ L` for `norm_SB` (`Defs/Block.lean:136`), `mul_Theta_of_three_le`, `zeroModeSet_*` | 1 |
| `d` | 3 | the pins carry `3 ≤ d →` (`Step6Pins.lean:225,246`); no step below uses `d`: `norm_SB` needs only `3 ≤ L`, `expHier_*` are stated for every `d` (`ExpHier.lean:722-748`); `ℓ^d ≥ 1` for any `d` | 0 (`d=3`), none needed |
| `|E|` | 1/2 | `|E| < 2` (pins), `|E| ≤ 2` (`norm_mul_mSigma_lt_one`, `zeroModeSet_Ugen`) | 3/2 |
| `(s, t)` | (1/4, 1/2) | `0 ≤ s ≤ t < 1` | `s`: 1/4 to 0; `t`: 1/2 to 1; `t-s = 1/4` |
| `‖u·cycProd‖`, `u ∈ [s,t]` | `u ≤ 1/2` (`|m(σ)| = 1`: `norm_mSigma`) | `< 1` for `ThetaN` slots, `thetaKer`/`uKer` identities (`Semicircle.lean:91`: `0 ≤ u < 1` suffices) | 1/2 |
| `ℓ_u = ellT L g u` | 1 on [s,t] (`g = 1/64`, `g/√(1/2) < 1`) | `1 ≤ ℓ_u`: `ellT = min (max (·) 1) L`, `1 ≤ L` (`RBM.one_le_ellT`, `Params.lean:39`; target 4c is the `ℕ`-cast form) | 0 on [s,t]; `ℓ_u ≤ L = 4` |
| `C, c` of `STMollifierProps` | any reals (the proof never uses their sign) | clause 4 gives `‖∂_uϑ‖ ≤ |C| (1-t)⁻¹` on `[s,t]` since `(1-u)⁻¹ ≤ (1-t)⁻¹`, `((ℓ^d)⁻¹)^1 ∈ (0,1]` (`m = 1`: tensors of 2 indices) | `|C|(1-t)⁻¹ = 2|C|` at `t = 1/2` |
| regularity of `ϑ` | `DifferentiableOn ℝ (ϑ·a) (Ico 0 1)` (clause 3) | continuity on `[s,t] ⊂ [0,1)` (also `s = 0`); `HasDerivAt` only at `u ∈ Ioo 0 1` (`Ico 0 1 ∈ 𝓝 u`); `∂_uϑ` measurable (`measurable_deriv`) + bounded ⇒ interval integrable; not continuous, not needed | none |

Per-target mathematics (checked against the merged definitions and RBM2D c9a24cf line numbers; each is a closed argument):

- 1a: `uKer μ r t = (1 - rμS)Θ_{tμ}` (`Evolution.lean:56`) is affine in `r`; `∂_r = -(μS)Θ_{tμ} = -thetaKer μ t` (`:52`). No hypothesis. RBM2D `MLExpDuhamel_hasDerivAt_ukerMat` `:55`. Sign checked.
- 1b: `uKer_eq_one_add` (`:90`, needs `‖tμ‖<1`, `3 ≤ L`): `uKer v t = 1 + (t-v)μ SΘ_t`; `Theta_sub_Theta` (`Deriv.lean:57`, needs `‖vμ‖,‖tμ‖<1`): `Θ_t - Θ_v = (t-v)μ Θ_t S Θ_v`. Hence `uKer v t · μSΘ_v = μSΘ_v + (t-v)μ² SΘ_tSΘ_v = μSΘ_t`. No commutation of `S` with `Θ` and no sign of `v,t` needed. (RBM2D `uker_mul_thetaGenMat` `MLExpVocab.lean:190`.)
- 1c: `𝒰_{v,t}(Θ^{(k)}_v A)_a = Σ_i Σ_{b,c} ∏_{j≠i}u_j(a_j,b_j) · u_i(a_i,b_i) θ_i(v)(b_i,c) A(update b i c)`; summing `b_i` first and 1b with `μ_i = cycProd i`, `‖vμ_i‖<1` (`norm_mul_mSigma_lt_one`, `0 ≤ v < 1`, `|E| ≤ 2`) gives `θ_i(t)(a_i,c)`: the statement of `expDuh_Ugen_ThetaN`. (RBM2D `:75`, `:96`.)
- 1d/1e/1f: product rule over `Fin k` (`HasDerivAt.fun_finsetProd`, 1a): `∂_v ∏_j u_j = -Σ_i (∏_{j≠i}u_j) θ_i(t)`, so by 1c `∂_v(𝒰_{v,t}Y_v) = 𝒰_{v,t}Y' - 𝒰_{v,t}Θ_vY_v` (`Ugen` additive: `GridDuhamelN_Ugen_add`; subtraction by the same linearity). Kernel entries are affine in `v`, so continuity of `Ugen` needs no time hypothesis; integrability = continuous × interval-integrable (`IntervalIntegrable.continuousOn_mul`), finite sum.
- 2a engine: `G(u) = (𝒰_{u,t}Y_u)_a`; for `u ∈ Ioo s t` (`0 ≤ u < 1`, `t < 1`) `G' = 𝒰_{u,t}(ΘY_u + D_u - ΘY_u) = 𝒰_{u,t}D_u`; `G` continuous on `Icc s t`; FTC `integral_eq_sub_of_hasDerivAt_of_le` (`FundThmCalculus.lean:1140`: `s ≤ t`, `ContinuousOn` on `Icc`, `HasDerivAt` on `Ioo`, `f'` interval integrable) gives `∫_s^t G' = G t - G s`; `G t = Y_t a` by `GridDuhamelN_Ugen_self` (`0 ≤ t < 1`). Matches the statement of `expDuh_duhamel`.
- 2b: `STthetaOp` has the same scalar `μ = m(σ₀)m(σ₁)` in both slots (`Step2Defs.lean:119`); `cycProd` at `k=2` gives `m₀m₁` and `m₁m₀` (`finRotate 2`), equal by `mul_comm`; `STmsig = mSigma` by `rfl` (`ExpHier.lean:375` is the private proof).
- 3 plain (A = ∅): continuity of `f, D` on `Ico 0 1 ⊇ Icc s t` (`t < 1`, includes `s = 0`), `HasDerivAt` on `Ioo 0 1 ⊇ Ioo s t` (`0 ≤ s`), the three public `expHier_*`; `D` continuous ⇒ interval integrable; engine.
- 3 zero mode: `Q^{(A)}` is the linear map `zeroModeSetLin` (`ZeroModeCalc.lean:101`) on a finite-dimensional space, so `HasDerivAt` and `ContinuousOn` pass entrywise. `∂Q f = Q(Θf + D) = ΘQf + QD` by `zeroModeSet_ThetaN` (`:395`, `‖u cycProd‖<1`, `3 ≤ L`) and `zeroModeSet_add`; engine with `Y = Qf`, source `QD`: `Q f_t = 𝒰_{s,t}Q f_s + ∫𝒰_{u,t}Q D_u`; then `zeroModeSet_Ugen` (`:450`, needs `0 ≤ t < 1`, second time `t` in both terms) turns it into the pin. `Q D` entries are finite linear combinations of entries of `D`: integrable.
- 4 `𝒬` algebra: `QopAlgebra_Qop_hasDerivAt` (`:643`) with `A' = Θf + D`: `∂(𝒬f) = 𝒬(Θf + D) - (𝒫f)_{a₀}∂ϑ`. `𝒬` is additive (`STQop`, `STPsum` finite sums), so `= Θ(𝒬f) + [𝒬D + (𝒬Θf - Θ𝒬f) - (𝒫f)∂ϑ] = Θ(𝒬f) + STExpQsrc` (`Step6Pins.lean:236-241`, sign `-` as in `6:115`). Sum-one (clause 1) is not used. Pin Q = engine at `Y = 𝒬f`, `D = STExpQsrc`.
- 4d integrability of `STExpQsrc` on `[s,t]`: `𝒬D` continuous; `[𝒬,Θ]f = Θ((𝒫f)ϑ) - (𝒫Θf)ϑ` (`QopAlgebra_commutator_ThetaN`, `:871`) continuous since `u ↦ Θ_{uμ}` has continuous entries (`continuousAt_Theta`, `‖uμ‖<1`) and `ϑ, f` are; `(𝒫f_u)_{a₀}` continuous times `∂_uϑ` (measurable and bounded on `[s,t]`): interval integrable.

Checklist §29/§45 O2: (1) time `0 ≤ s ≤ t < 1`, continuity on `[s,t]` incl. `s = 0`, drift identity only on `(s,t) ⊂ (0,1)`: holds as above. (2)-(7): no regime, no window, no `L`-`W` relation (`3 ≤ L` = `sz.three_le_L n`, `Sizes.lean:145`), no `∀ᶠ` in the pins (the `∀ᶠ` of `STExpDuhEqQ` is in `st6_duhEqQ_of_pin`'s `filter_upwards [hϑ]`, `Step6Kit.lean:838`), pointwise in `u`, `lam n` arbitrary, no scale `N`.
Consumers: `inst_duhamelZ (h : STExpDuhamelZ 3)` applies `h (by norm_num) sz0 0 (1/2) _ (1/4) (1/2) _ _ _ ![true,false] univ ![0, Pi.single 0 1]` (`Step6Pins.lean:668-678`, binder order of `STExpDuhamelZ` as printed at `:225`); `inst_duhamelQ` obtains `C c ϑ` from `stMollifierEx_holds` and applies `h … C c ϑ hϑ (1/4) (1/2)` (`:681-695`); `st6_duhEq_of_pin` applies the Z pin at `s n`, `u ∈ [s n, t n]`, `u < 1` from `st5_t_lt_one` (`Step6Kit.lean:361-367`), `st6_duhEqQ_of_pin` likewise for Q (`:833-841`).
Registry: `Test/Axioms.lean` on this `main` (cd6fcba) has the two owed lines at `:228-229` (identified by text). The line the ticket calls `:230` (`STExpLKLKHi`) is already gone (T2222 merged: `:230` is `STExpDriftLo`; only `STExpLKLKHiConcl` remains, `:321`); the hunk context for the deletion differs from the ticket's text, content of the two deleted lines does not.

### (ii) One concrete nondegenerate instance

Data (Lean instance data `sz0`, `n = 0`): `d = 3`, `L = 4`, `W = 32`, `lam = g = 1/64`, `E = 1/2`, `s = 1/4`, `t = 1/2`, `k = 2`, `σ ∈ {(+,-), (+,+), (-,+)}`, `A ∈ {∅,{0},{1},{0,1}}`, 64 sites. External hypotheses: none (`STExpHier` is proved, T2218). The one structural hypothesis of pin Q, `STMollifierProps`, is witnessed in Lean by the merged `stMollifierEx_holds`; the script gives an explicit surrogate `ϑ_t = (1-t²)δ_{a₀a₁} + t²/64` (`C = 200, c = 1`) satisfying clauses 1-4 on a grid of 508 times in `[0,1)` including `1-10⁻¹¹`. The script solves `Y' = Θ_uY + D_u` with an independent RK solver (DOP853, rtol 1e-12) and compares with the Duhamel right side (24-point Gauss-Legendre); it tests 1a-1d, the engine, zero mode, `𝒬`-Duhamel; `S = SB` is built from `sbKernel` (`Block.lean:38`), `m(E)` from `mE` (`Semicircle.lean:38`).

```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2224/inst.py | head -17
n sites 64  max|rowsum-1| 1.1102230246251565e-16  symmetric True
sigma (True, False)  |mu| 1.0  ||u mu|| on [s,t] max 0.5 <1
  (1a) d_r uKer = -thetaKer : 2.7229751786705947e-10
  (1b) uKer(v,t) thetaKer(v) = thetaKer(t) : 2.4424906541753444e-15
  (1c) Ugen_{v,t} ThetaN_v A = slotwise sum : 2.7056661287843684e-14
  (1d) d_v Ugen_{v,t}Y_v = Ugen(Y' - Theta Y) : 1.7897116908568101e-09
  engine: Y_t = U_{s,t}Y_s + int U_{u,t}D_u : 3.8944686850978474e-14
  Ugen_{t,t} = id : 6.764165321960921e-15
  zero-mode A=(): Q f_t = Q U f_s + int Q U D : 3.89e-14; Q commutes with U: 0.00e+00
  zero-mode A=(0,): Q f_t = Q U f_s + int Q U D : 3.92e-14; Q commutes with U: 1.07e-14
  zero-mode A=(1,): Q f_t = Q U f_s + int Q U D : 3.88e-14; Q commutes with U: 1.25e-14
  zero-mode A=(0, 1): Q f_t = Q U f_s + int Q U D : 3.89e-14; Q commutes with U: 9.77e-15
  Q-Duhamel: Q_t f_t = U Q_s f_s + int U A_u : 8.511836204055115e-14
  mollifier: clause1 sum_a1 vartheta =1 : 2.220446049250313e-16 ; clause2 max ratio 0.031454870260511185 ; clause4 max ratio 0.00246093502918914 (<=1 needed); ell on [s,t]: 1.0 1.0
sigma (True, True)  |mu| 1.0  ||u mu|| on [s,t] max 0.5 <1
  (1a) d_r uKer = -thetaKer : 1.603219586372017e-10
  (1b) uKer(v,t) thetaKer(v) = thetaKer(t) : 7.11431226040132e-16
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2224/inst.py | sed -n '18,$p' | grep -E "sigma|\(1b\)|engine|A=\(0, 1\)"
  engine: Y_t = U_{s,t}Y_s + int U_{u,t}D_u : 7.27989956159526e-15
  zero-mode A=(0, 1): Q f_t = Q U f_s + int Q U D : 6.88e-15; Q commutes with U: 2.84e-15
sigma (False, True)  |mu| 1.0  ||u mu|| on [s,t] max 0.5 <1
  (1b) uKer(v,t) thetaKer(v) = thetaKer(t) : 2.4424906541753444e-15
  engine: Y_t = U_{s,t}Y_s + int U_{u,t}D_u : 4.051412174628364e-14
  zero-mode A=(0, 1): Q f_t = Q U f_s + int Q U D : 3.99e-14; Q commutes with U: 9.93e-15
```

(1a),(1d) errors ~1e-9 are central finite-difference error (h = 1e-6, 1e-5); all other residuals ≤ 1e-13. Instance is nondegenerate: `L^d = 64`, `s < t`, `‖u μ‖ ≤ 1/2`, `Y_s`, `D` random complex, `A` includes `{0,1}`.

### Verdicts

- Target 1 (kernel: 1a-1f): PASS. Target 2 (engine, bridge): PASS. Target 3 (plain, zero-mode, `stExpDuhamelZ_holds`): PASS. Target 4 (`𝒬`: 4a-4e): PASS. Target 5 (five instances, `d = 3`, `sz0`, `n = 0`, `E = 1/2`): PASS; `inst_expDuh_plain` uses `s = 0` (only continuity there: engine needs only `Icc` continuity), `inst_expDuh_single` `A = {1}`, `σ = (-,+)`: both inside the numeric instance above.
- No statement of check section 2 is false, no hypothesis set is unsatisfiable, no external input missing, no paper-delta candidate.

## (b) Script output
```
# Script output written Mon Oct  5 23:19:26 UTC 2026; branch t/T2224, commit a4d0978, worktree /Users/junyin/Lean_proof/RBM3D-wt/T2224
# == Branch content (files, size, hygiene) ==
$ git log -1 --format="%h %an <%ae> %s"; git diff --stat main...t/T2224; git diff main -- RBM3D/Induction/Step6Pins.lean | wc -l; git diff main...t/T2224 -- RBM3D/Test/Axioms.lean | grep "^[-+][^-+]" | cut -c1-110
a4d0978 Jun Yin <321276894+JYin80@users.noreply.github.com> T2224: S6-05 Induction/ExpDuhamel (proves STExpDuhamelZ, STExpDuhamelQ)
 RBM3D/Induction/ExpDuhamel.lean | 798 ++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean          |   2 -
 2 files changed, 798 insertions(+), 2 deletions(-)
       0
-   `RBM.Gauss.Sizes.STExpDuhamelZ, -- `6:3-7`, `6:142-146` Duhamel form: S6-05; S6-01 (T2204, DECISIONS §67: 
-   `RBM.Gauss.Sizes.STExpDuhamelQ, -- `6:109-116` Duhamel form with Q: S6-05; S6-01 (T2204, DECISIONS §67: ow
$ grep -cE "\bsorry\b|\badmit\b|native_decide|^axiom " RBM3D/Induction/ExpDuhamel.lean; wc -l RBM3D/Induction/ExpDuhamel.lean
0
     798 RBM3D/Induction/ExpDuhamel.lean
# == Build of the new module (the info lines are the file's own #print axioms) ==
$ lake build RBM3D.Induction.ExpDuhamel 2>&1 | tail -2 | cut -c1-150
info: RBM3D/Induction/ExpDuhamel.lean:798:0: 'RBM.Gauss.Step6Inst.inst_expDuh_single' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3854 jobs).
$ lake build RBM3D.Induction.ExpDuhamel 2>&1 | grep -c "warning: RBM3D/Induction/ExpDuhamel"   # warnings of this file
0
# == Axioms: #print axioms of every public declaration (17 targets + 5 instances) ==
$ lake env lean RBM3D/Induction/ExpDuhamel.lean > axioms.out 2>&1; echo "exit $?"; grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" axioms.out; grep -vc "depends on axioms: \[propext, Classical.choice, Quot.sound\]" axioms.out
exit 0
22
0
# == Target statements (extracted by script from the file: header through the colon-equals; line numbers of the file) ==
$ python3 extract.py targets   # 17 theorems of RBM.Gauss.Sizes
71: theorem expDuh_hasDerivAt_uKer {d L : ℕ} [NeZero L] (g : ℝ) (μ : ℂ) (t : ℝ) (x y : Zd d L) (v : ℝ) : HasDerivAt (fun r : ℝ => RBM.uKer d L g μ r t x y) (-(RBM.thetaKer d L g μ t x y)) v
89: theorem expDuh_uKer_mul_thetaKer {d L : ℕ} [NeZero L] (g : ℝ) (hL : 3 ≤ L) {μ : ℂ} {v t : ℝ} (hv : ‖(v : ℂ) * μ‖ < 1) (ht : ‖(t : ℂ) * μ‖ < 1) : RBM.uKer d L g μ v t * RBM.thetaKer d L g μ v = RBM.thetaKer d L g μ t
198: theorem expDuh_Ugen_ThetaN {d L : ℕ} [NeZero L] (g : ℝ) (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {k : ℕ} (σ : Fin k → Bool) {v t : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (ht0 : 0 ≤ t) (ht1 : t < 1) (A : (Fin k → Zd d L) → ℂ) (a : Fin k → Zd d L) : RBM.Ind.Ugen d L g E σ v t (RBM.ThetaN d L g (fun l => RBM.mSigma E (σ l)) v A) a = ∑ b : Fin k → Zd d L, (∑ i : Fin k, (∏ j ∈ Finset.univ.erase i, RBM.uKer d L g (RBM.cycProd (fun l => RBM.mSigma E (σ l)) j) v t (a j) (b j)) * RBM.thetaKer d L g (RBM.cycProd (fun l => RBM.mSigma E (σ l)) i) t (a i) (b i)) * A b
210: theorem expDuh_hasDerivAt_Ugen {d L : ℕ} [NeZero L] (g : ℝ) (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {k : ℕ} (σ : Fin k → Bool) {u t : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (ht0 : 0 ≤ t) (ht1 : t < 1) {Y : ℝ → (Fin k → Zd d L) → ℂ} {Y' : (Fin k → Zd d L) → ℂ} (hY : ∀ b, HasDerivAt (fun v => Y v b) (Y' b) u) (a : Fin k → Zd d L) : HasDerivAt (fun v => RBM.Ind.Ugen d L g E σ v t (Y v) a) (RBM.Ind.Ugen d L g E σ u t (fun b => Y' b - RBM.ThetaN d L g (fun l => RBM.mSigma E (σ l)) u (Y u) b) a) u
265: theorem expDuh_continuousOn_Ugen {d L : ℕ} [NeZero L] (g E : ℝ) {k : ℕ} (σ : Fin k → Bool) (t : ℝ) {S : Set ℝ} {Y : ℝ → (Fin k → Zd d L) → ℂ} (hY : ∀ b, ContinuousOn (fun v => Y v b) S) (a : Fin k → Zd d L) : ContinuousOn (fun v => RBM.Ind.Ugen d L g E σ v t (Y v) a) S
276: theorem expDuh_intervalIntegrable_Ugen {d L : ℕ} [NeZero L] (g E : ℝ) {k : ℕ} (σ : Fin k → Bool) (s t : ℝ) {D : ℝ → (Fin k → Zd d L) → ℂ} (hD : ∀ b, IntervalIntegrable (fun u => D u b) MeasureTheory.volume s t) (a : Fin k → Zd d L) : IntervalIntegrable (fun u => RBM.Ind.Ugen d L g E σ u t (D u) a) MeasureTheory.volume s t
299: theorem expDuh_duhamel {d L : ℕ} [NeZero L] (g : ℝ) (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {k : ℕ} (σ : Fin k → Bool) {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t < 1) {Y D : ℝ → (Fin k → Zd d L) → ℂ} (hYc : ∀ b, ContinuousOn (fun u => Y u b) (Set.Icc s t)) (hDi : ∀ b, IntervalIntegrable (fun u => D u b) MeasureTheory.volume s t) (hYd : ∀ u ∈ Set.Ioo s t, ∀ b, HasDerivAt (fun v => Y v b) (RBM.ThetaN d L g (fun l => RBM.mSigma E (σ l)) u (Y u) b + D u b) u) (a : Fin k → Zd d L) : Y t a = RBM.Ind.Ugen d L g E σ s t (Y s) a + ∫ u in s..t, RBM.Ind.Ugen d L g E σ u t (D u) a
327: theorem expDuh_STthetaOp_eq_ThetaN {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool) (A : (Fin 2 → Zd d (sz.L n)) → ℂ) (a : Fin 2 → Zd d (sz.L n)) : sz.STthetaOp n E u σ A a = RBM.ThetaN d (sz.L n) (sz.lam n) (fun l => RBM.mSigma E (σ l)) u A a
349: theorem expDuh_zeroModeSet_hasDerivAt {d L : ℕ} [NeZero L] {k : ℕ} (A : Finset (Fin k)) {Y : ℝ → (Fin k → Zd d L) → ℂ} {Y' : (Fin k → Zd d L) → ℂ} {u : ℝ} (hY : ∀ b, HasDerivAt (fun v => Y v b) (Y' b) u) (a : Fin k → Zd d L) : HasDerivAt (fun v => RBM.zeroModeSet d L A (Y v) a) (RBM.zeroModeSet d L A Y' a) u
358: theorem expDuh_zeroModeSet_continuousOn {d L : ℕ} [NeZero L] {k : ℕ} (A : Finset (Fin k)) {Y : ℝ → (Fin k → Zd d L) → ℂ} {S : Set ℝ} (hY : ∀ b, ContinuousOn (fun v => Y v b) S) (a : Fin k → Zd d L) : ContinuousOn (fun v => RBM.zeroModeSet d L A (Y v) a) S
367: theorem expDuh_plain {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| < 2) (s t : ℝ) (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t < 1) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : sz.STExpErr n E t σ a = RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ s t (fun b => sz.STExpErr n E s σ b) a + ∫ u in s..t, RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ u t (fun b => sz.STExpDrift n E u σ b) a
385: theorem stExpDuhamelZ_holds (d : ℕ) : STExpDuhamelZ d
435: theorem expDuh_continuousOn_Qop {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| < 2) {C c : ℝ} {ϑ : ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ} (hϑ : STMollifierProps (d := d) (sz.lam n) C c ϑ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ContinuousOn (fun u => STQop (d := d) ϑ u (fun b => sz.STExpErr n E u σ b) a) (Set.Ico 0 1)
443: theorem expDuh_Qop_hasDerivAt {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| < 2) {C c : ℝ} {ϑ : ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ} (hϑ : STMollifierProps (d := d) (sz.lam n) C c ϑ) (σ : Fin 2 → Bool) (u : ℝ) (hu : u ∈ Set.Ioo (0 : ℝ) 1) (a : Fin 2 → Zd d (sz.L n)) : HasDerivAt (fun v => STQop (d := d) ϑ v (fun b => sz.STExpErr n E v σ b) a) (sz.STthetaOp n E u σ (STQop (d := d) ϑ u (fun b => sz.STExpErr n E u σ b)) a + sz.STExpQsrc n E u σ ϑ a) u
462: theorem expDuh_one_le_ellT (L : ℕ) (g t : ℝ) (hL : 1 ≤ L) : 1 ≤ RBM.ellT L g t
528: theorem expDuh_intervalIntegrable_Qsrc {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| < 2) {C c : ℝ} {ϑ : ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ} (hϑ : STMollifierProps (d := d) (sz.lam n) C c ϑ) (σ : Fin 2 → Bool) {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t < 1) (b : Fin 2 → Zd d (sz.L n)) : IntervalIntegrable (fun u => sz.STExpQsrc n E u σ ϑ b) MeasureTheory.volume s t
570: theorem stExpDuhamelQ_holds (d : ℕ) : STExpDuhamelQ d
# == The five instances (statements as extracted; equal to check section 3, see the equality run below) ==
$ python3 extract.py inst
599: theorem inst_duhamelZ_holds : RBM.zeroModeSet 3 (sz0.L 0) (Finset.univ : Finset (Fin 2)) (fun b => sz0.STExpErr 0 (1 / 2) (1 / 2) ![true, false] b) ![0, Pi.single 0 1] = RBM.zeroModeSet 3 (sz0.L 0) (Finset.univ : Finset (Fin 2)) (RBM.Ind.Ugen 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ![true, false] (1 / 4) (1 / 2) (fun b => sz0.STExpErr 0 (1 / 2) (1 / 4) ![true, false] b)) ![0, Pi.single 0 1] + ∫ u in (1 / 4 : ℝ)..(1 / 2 : ℝ), RBM.zeroModeSet 3 (sz0.L 0) (Finset.univ : Finset (Fin 2)) (RBM.Ind.Ugen 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ![true, false] u (1 / 2) (fun b => sz0.STExpDrift 0 (1 / 2) u ![true, false] b)) ![0, Pi.single 0 1]
611: theorem inst_duhamelQ_holds : ∃ (C c : ℝ) (ϑ : ℝ → (Fin 2 → Zd 3 (sz0.L 0)) → ℂ), STMollifierProps (d := 3) (sz0.lam 0) C c ϑ ∧ STQop (d := 3) ϑ (1 / 2) (fun b => sz0.STExpErr 0 (1 / 2) (1 / 2) ![true, false] b) ![0, Pi.single 0 1] = RBM.Ind.Ugen 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ![true, false] (1 / 4) (1 / 2) (STQop (d := 3) ϑ (1 / 4) (fun b => sz0.STExpErr 0 (1 / 2) (1 / 4) ![true, false] b)) ![0, Pi.single 0 1] + ∫ u in (1 / 4 : ℝ)..(1 / 2 : ℝ), RBM.Ind.Ugen 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ![true, false] u (1 / 2) (sz0.STExpQsrc 0 (1 / 2) u ![true, false] ϑ) ![0, Pi.single 0 1]
621: theorem inst_duhEq_holds : STExpDuhEq sz0 (STflowE z0) sInst tInst
625: theorem inst_expDuh_plain : sz0.STExpErr 0 (1 / 2) (1 / 2) ![true, true] ![0, Pi.single 0 1] = RBM.Ind.Ugen 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ![true, true] 0 (1 / 2) (fun b => sz0.STExpErr 0 (1 / 2) 0 ![true, true] b) ![0, Pi.single 0 1] + ∫ u in (0 : ℝ)..(1 / 2 : ℝ), RBM.Ind.Ugen 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ![true, true] u (1 / 2) (fun b => sz0.STExpDrift 0 (1 / 2) u ![true, true] b) ![0, Pi.single 0 1]
635: theorem inst_expDuh_single : RBM.zeroModeSet 3 (sz0.L 0) ({1} : Finset (Fin 2)) (fun b => sz0.STExpErr 0 (1 / 2) (1 / 2) ![false, true] b) ![0, Pi.single 0 1] = RBM.zeroModeSet 3 (sz0.L 0) ({1} : Finset (Fin 2)) (RBM.Ind.Ugen 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ![false, true] 0 (1 / 2) (fun b => sz0.STExpErr 0 (1 / 2) 0 ![false, true] b)) ![0, Pi.single 0 1] + ∫ u in (0 : ℝ)..(1 / 2 : ℝ), RBM.zeroModeSet 3 (sz0.L 0) ({1} : Finset (Fin 2)) (RBM.Ind.Ugen 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ![false, true] u (1 / 2) (fun b => sz0.STExpDrift 0 (1 / 2) u ![false, true] b)) ![0, Pi.single 0 1]
# == Lower-level theorems at the same data (compiled examples, d = 3, sz0, n = 0, E = 1/2; hierarchy f, D of sz0, mollifier of stMollifierEx_holds) ==
$ grep -o "^-- [1-4][a-f] at\|^-- [1-4][a-f] on" RBM3D/Induction/ExpDuhamel.lean | cut -c4-5 | paste -sd" " -; grep -c "^example" RBM3D/Induction/ExpDuhamel.lean   # labels of the 14 examples; number of examples
1a 1b 1c 1d 1e 1f 2a 2b 3b 3c 4a 4b 4c 4d
14
# == Check-file equality (scratch = check imports + import RBM3D.Induction.ExpDuhamel + sections 1-2 + 17 + 2 + 5 equality examples) ==
$ lake env lean check_eq.lean > check_eq.out 2>&1; echo "exit $?"   # check_eq.lean in the scratchpad, not in the repo
exit 0
$ grep -c "^example : RBM.Gauss.Sizes.T2224Check" check_eq.lean; grep -c "^  @RBM.Gauss.Step6Inst.inst_" check_eq.lean; grep -c "^example (d : ℕ) : RBM.Gauss.Sizes.STExpDuhamel" check_eq.lean; grep -c "error" check_eq.out
17
5
2
0
# == Full build (CLAUDE.md 3(A) step 5; DECISIONS 20): the root does not import the new module until the hub merges, so the run used a temporary uncommitted import line after the last import of RBM3D.lean ==
started Mon Oct  5 23:10:20 UTC 2026 (tool log), on the tree before the final docstring-citation amend
$ lake build   # temporary line: import RBM3D.Induction.ExpDuhamel; exit code 0
 RBM.Univ.UNTrLocalInit].
non-vacuity certificates: 0 of 144 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4027 jobs).
$ git status --short RBM3D.lean   # after removing the temporary line (empty)
# == Registry pre-check (DECISIONS 20 (2)): pre_new.lean = import RBM3D; import RBM3D.Induction.ExpDuhamel; #assert_rbm_axioms; pre_base = the same file run before Test.Axioms was rebuilt ==
$ date -u; lake env lean pre_new.lean > pre_new.out 2>&1; echo "exit $?"   # pre_base.out: same file run at Mon Oct  5 23:09:27 UTC 2026 (tool log), exit 0
Mon Oct  5 23:19:40 UTC 2026
exit 0
$ grep -n "STExpDuhamelZ\|STExpDuhamelQ" pre_base.out | cut -c1-90
137:  RBM.Gauss.Sizes.STExpDuhamelZ: 16 [no certificate]
138:  RBM.Gauss.Sizes.STExpDuhamelQ: 6 [no certificate]
206: RBM.Gauss.Sizes.STExpDuhamelZ,
207: RBM.Gauss.Sizes.STExpDuhamelQ,
$ grep -c "STExpDuhamel" pre_new.out   # owed ledger and carry-nothing list
0
$ grep "premises found\|^registry" pre_base.out pre_new.out | cut -c1-118
pre_base.out:premises found by scanning: 124 (borrowed 1, owed 91, structural 26, refuted 6).
pre_base.out:registry: 2 borrowed + 144 owed + 81 structural + 7 refuted; 110 registered premise(s) carry nothing yet:
pre_new.out:premises found by scanning: 124 (borrowed 1, owed 91, structural 26, refuted 6).
pre_new.out:registry: 2 borrowed + 142 owed + 81 structural + 7 refuted; 108 registered premise(s) carry nothing yet: 
$ grep -c "none of" pre_new.out   # unregistered premise message
0
# == Name-clash grep of the new public (and private) names, sorry/axiom grep ==
$ bash clash.sh
declarations in ExpDuhamel.lean:       39
files other than ExpDuhamel.lean mentioning any of them (grep -rlwE over RBM3D/, RBM3D.lean):
hits:        0
sorry/admit/native_decide/axiom in ExpDuhamel.lean: 0
# == Ports: RBM2D Evolution/MLExpDuhamel.lean at c9a24cf (line numbers there) -> this file (no RBM1D port) ==
$ bash portmap.sh | paste -d"|" - -   # RBM2D name :line  ->  RBM3D name :line
M_ukerMat_eq :50->expDuh_uKer_eq :66|M_hasDerivAt_ukerMat :55->expDuh_hasDerivAt_uKer :71
M_continuous_ukerMat :67->expDuh_continuous_uKer :83|M_sum_update_reindex :75->expDuh_sum_update_reindex :111
MLExpVocab:uker_mul_thetaGenMat :190->expDuh_uKer_mul_thetaKer :89|M_Uker_theta :96->expDuh_Uker_theta :131
M_norm_xi :167->expDuh_norm_slot :192|M_continuousOn_Ugen :174->expDuh_continuousOn_Ugen :265
M_ftc :188->expDuh_duhamel :299|M_continuousAt_Theta_entry :285->expDuh_continuousAt_Theta_entry :498
M_continuousOn_thetaGenMat :294->expDuh_continuousOn_thetaKer :508|M_continuousOn_thetaSig :303->expDuh_continuousOn_ThetaN :517
M_continuousOn_Qop :320->expDuh_continuousOn_Qop_gen :425|M_hasDerivAt_Qop :367->expDuh_Qop_hasDerivAt :443
MLExpVocab:qop_source :229->expDuh_Qop_hasDerivAt :443|M_continuousOn_qDriftT :387->expDuh_intervalIntegrable_Qsrc :528
expDuhamelPin_of_hier :412->stExpDuhamelZ_holds :385|expQDuhamelPin_of_hier :423->stExpDuhamelQ_holds :570
$ git -C ../RBM2D --no-optional-locks log -1 --format="RBM2D HEAD %h"; git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Evolution/MLExpDuhamel.lean RBM2D/Evolution/MLExpVocab.lean
RBM2D HEAD 9e0f275
 RBM2D/Evolution/MLExpDuhamel.lean | 126 ++-----
 RBM2D/Evolution/MLExpVocab.lean   | 757 +++++---------------------------------
 2 files changed, 105 insertions(+), 778 deletions(-)
# == Merge note: main moved after this branch's base ==
$ git log --oneline -1 cd6fcba; git log --oneline cd6fcba..main; git merge-tree --write-tree --no-messages main t/T2224 >/dev/null; echo "merge-tree rc=$?"
cd6fcba T2222: merge S6-06 Induction/ExpEtermsA (proves STExpLKLKHi)
f2766db T2223: merge S6-11 Induction/ExpIniI (STExpIniI')
merge-tree rc=0
```

### Narrative (facts; the evidence is the script output above)

1. Delivered: `RBM3D/Induction/ExpDuhamel.lean` (798 lines; ticket estimate 650 / 820 / 1050): 17 public theorems in `RBM.Gauss.Sizes` (each equal to the same-named def of check section 2, compiled), 5 public instances in `RBM.Gauss.Step6Inst`, 14 further compiled `example`s that apply the lower-level theorems 1a-1f, 2a, 2b, 3b, 3c, 4a-4d at the same data, and 17 private helpers prefixed `expDuh_`. `Test/Axioms.lean`: exactly the two owed lines deleted.
2. Both pins hold for every `d`; the premise `3 ≤ d` of the pins is not used (every lemma is stated for all `d`; `3 ≤ L` is `sz.three_le_L n`). `git diff main -- RBM3D/Induction/Step6Pins.lean` is empty.
3. Target 1b is not a port of `uker_mul_thetaGenMat` (`MLExpVocab:190`): it follows from the merged `uKer_eq_one_add` and `Theta_sub_Theta`: `(1 - vμS)Θ_t · μSΘ_v = μSΘ_v + (t-v)μ² SΘ_tSΘ_v = μSΘ_t`; no commutation of `S` with `Θ`, no sign of `v, t`.
4. Targets 1c/1d port `MLExpDuhamel_Uker_theta` and the derivative part of `MLExpDuhamel_ftc` with slot parameters `ξ i = cycProd (fun l => mSigma E (σ l)) i` (private general lemma `expDuh_Uker_theta`) and labels `Fin k → Zd d L`; `k` is arbitrary (RBM2D carries `[NeZero k]`, `MLExpDuhamel_c9a24cf.lean:160`).
5. Engine 2a: continuity on `Icc s t`, derivative on `Ioo s t`, FTC from `s`, `Y_t = 𝒰_{t,t} Y_t` by `GridDuhamelN_Ugen_self`; the source is only interval integrable (1f: continuous kernel entries times integrable, finite sum).
6. Zero modes: `Q^{(A)}` is the `ℝ`-continuous linear map `LinearMap.toContinuousLinearMap ((zeroModeSetLin A).restrictScalars ℝ)` (finite dimensional), so derivative and continuity pass entrywise (`hasDerivAt_pi`, `continuousOn_pi`); `∂(Q f) = Θ(Q f) + Q D` by `zeroModeSet_add`, `zeroModeSet_ThetaN` (`‖u·cycProd‖ < 1`); `Q 𝒰 = 𝒰 Q` by `zeroModeSet_Ugen` at the second time `t < 1`, on both terms.
7. `𝒬` with the abstract `ϑ`: `ϑ` is differentiable only on `[0,1)` (third conjunct), so continuity is used on `Ico 0 1` (including `s = 0`) and `HasDerivAt` only at `u ∈ Ioo 0 1` (`Ico_mem_nhds`). `∂_uϑ` is interval integrable by `measurable_deriv`, the fourth conjunct, `1 ≤ ℓ_u` (`expDuh_one_le_ellT`) and `(1-u)⁻¹ ≤ (1-t)⁻¹`: bound `|C| (1-t)⁻¹`, no sign of `C, c`; the sum-one clause is not used.
8. Route difference to section (a), 4d: `QopAlgebra_commutator_ThetaN` is not used; continuity of `𝒬Θf` and `Θ𝒬f` is proved directly (entries of `Θ` by `continuousAt_Theta`). No statement changes; (a) needs no correction.
9. Consumers (§45 O2): `inst_duhamelZ`, `inst_duhEq`, `inst_duhamelQ` accept `stExpDuhamelZ_holds 3`, `stExpDuhamelQ_holds 3` (instances `inst_duhamelZ_holds`, `inst_duhEq_holds`, `inst_duhamelQ_holds`); `inst_skeleton6I..IV`, `st6_duhEq_of_pin`, `st6_duhEqQ_of_pin` take the same `Prop`s (equality examples `STExpDuhamelZ d`, `STExpDuhamelQ d`); they are not re-instantiated here.
10. Registry and full build: see the script output (two names gone from the owed ledger; owed 144 -> 142; no unregistered premise); the full build needed a temporary root import, removed afterwards (`git status --short RBM3D.lean` empty). The root import is the hub's step at merge.

## (c) Verified Mathlib names used (module of each name, by script; `#check @name` of all 39 compiled)
```
$ lake env lean mathlib_check.lean > mathlib_check.out 2>&1; echo "exit $?"; grep -c "#check" mathlib_check.lean; grep -c error mathlib_check.out
exit 0
39
0
$ lake env lean mods.lean   # #eval over Environment.getModuleIdxFor?, one line per module
MeasureTheory.Integral.IntervalIntegral.FundThmCalculus: intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
Analysis.Calculus.FDeriv.Measurable: measurable_deriv
Analysis.Calculus.Deriv.Mul: HasDerivAt.fun_finsetProd HasDerivAt.mul_const
MeasureTheory.Integral.IntervalIntegral.Basic: IntervalIntegrable.continuousOn_mul ContinuousOn.intervalIntegrable_of_Icc IntervalIntegrable.sum IntervalIntegrable.add IntervalIntegrable.sub intervalIntegrable_iff_integrableOn_Icc_of_le
Analysis.Calculus.Deriv.Prod: hasDerivAt_pi
Topology.ContinuousOn: continuousOn_pi Continuous.comp_continuousOn
Topology.Algebra.Module.FiniteDimension: LinearMap.toContinuousLinearMap
Algebra.Module.LinearMap.Defs: LinearMap.restrictScalars
Analysis.Calculus.Deriv.Comp: HasFDerivAt.comp_hasDerivAt
Analysis.Calculus.FDeriv.Linear: ContinuousLinearMap.hasFDerivAt
MeasureTheory.Integral.IntegrableOn: MeasureTheory.Measure.integrableOn_of_bounded
MeasureTheory.Measure.Restrict: MeasureTheory.ae_restrict_iff'
MeasureTheory.Measure.Lebesgue.Basic: Real.volume_Icc
Algebra.Order.GroupWithZero.Basic: inv_anti₀ pow_le_one₀ inv_le_one_of_one_le₀ one_le_pow₀
Data.Nat.Cast.Order.Basic: Nat.one_le_cast
Analysis.Calculus.Deriv.Add: HasDerivAt.fun_sum HasDerivAt.fun_sub
Analysis.Complex.RealDeriv: HasDerivAt.ofReal_comp
Topology.Algebra.Monoid: continuous_finsetProd continuousOn_finsetSum
Topology.Order.OrderClosed: Ico_mem_nhds
Analysis.Calculus.FDeriv.Basic: DifferentiableOn.differentiableAt DifferentiableOn.continuousOn
Analysis.Calculus.Deriv.Basic: DifferentiableAt.hasDerivAt HasDerivAt.congr_deriv
Algebra.BigOperators.Group.Finset.Defs: Finset.sum_nbij'
Algebra.BigOperators.Group.Finset.Basic: Finset.mul_prod_erase
Logic.Function.Basic: Function.update_idem Function.update_eq_self
```

## (d) Open issues and paper-delta candidates

- Open issues: none. Paper-delta candidates: none (`T2224a...` not needed: no step needed a hypothesis a pin lacks; the sign of `-(𝒫 f) ∂_uϑ` is the merged pin's, existing T2166a).
- Observations for the hub: (i) `main` moved to `f2766db` (T2223) after this branch's base `cd6fcba`; `git merge-tree` reports a clean merge (rc 0, script output above); the `Axioms.lean` hunk of this branch is the two deleted lines at `:228-229`. (ii) RBM2D `HEAD` is `9e0f275`, not `c9a24cf`; line numbers cited are those of `c9a24cf` (copy of the file read with `git show`).
