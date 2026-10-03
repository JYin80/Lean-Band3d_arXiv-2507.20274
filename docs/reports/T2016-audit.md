Auditor model: claude-opus-5-5

# T2016 audit (EK-D1, report-only design), round 1 — Sat Oct  3 04:02:46 UTC 2026
Branch `t/T2016` at `c961e62`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2016-audit1` (detached).
Targets: the seven pins `EKSumNdecay`, `EKSumDecay1`, `EKSumDecayNAL`, `EKSumDecay2`, `EKSumDecayNonzero`, `EKPropT`, `EKTTk`; the skeleton `ekSumDecay1_two` (item 6); instances (item 9).

## 1. Build, axioms, scope
```
$ git -C /Users/junyin/Lean_proof/RBM3D diff --stat main...t/T2016
 RBM3D/Probe/T2016Pins.lean | 1673 ++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1673 insertions(+)
$ lake build RBM3D.Probe.T2016Pins 2>&1 | grep -E "^(warning|error)|Build completed|uild failed"
Build completed successfully (2544 jobs).
$ lake env lean RBM3D/Probe/T2016Pins.lean ; echo EXIT $?     (non-axiom lines)
EXIT 0
$ grep -c "depends on axioms" out ; grep "depends on axioms" out | grep -vc "\[propext, Classical.choice, Quot.sound\]"
27
0
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom\b" RBM3D/Probe/T2016Pins.lean
(no output)
$ awk 'NR>1109 && /^\/-|^-\/$/' ...   (scripts appendix is one comment block after `end RBM`)
1118: /-
1673: -/
```
Selected axiom lines: `ekSumNdecay_holds`, `ekPropT_holds`, `ekTTk_holds`, `ekSumDecay1_two`, `ekInstNdecay`, `ekInstDecay1`, `ekInstNAL`, `ekInstDecay2`, `ekInstNonzero`, `ekInstPropT`, `ekInstTTk`: all `[propext, Classical.choice, Quot.sound]`.
Only the sole writable Lean file is touched; no merged file, no frozen signature changed. The prove report is the other sole writable file (main worktree).

## 2. Statements against the paper (TeX `3_5:1615–1700`, `3_5:109–135`, `3_5:311–340`, `7_8:1661–1666`, `1_2:1107,1121`)
Definitions used by the pins, checked against the paper:
```
Evolution.lean:49  cycProd m i = m i * m (finRotate n i)           = M^(σi,σi+1), cyclic σ_{n+1}=σ_1
Evolution.lean:56  uKer μ s t = (1 - (s μ)•SB) * Theta(t μ)         = (1-sMS)/(1-tMS)   (def_Ustz)
Evolution.lean:65  UN m s t A a = Σ_b (∏_i uKer(cycProd m i)(a i)(b i)) A b        (def_Ustz)
Evolution.lean:194 zeroModeOp i A a = A a - avgOp i A a ; zeroModeSet = ∏_{i∈A} Q^(i)   (def;zero_mode_remove)
Params.lean:32     ellT = min (max (g/√|1-t|) 1) L                  = (eq:ellt)
Params.lean:36     Bparam = (g²+|1-t|)⁻¹(K+1)^{-(d-2)} + (L^d|1-t|)⁻¹  = (eq_B_param)
Tail.lean:48       tailT r = BparamR r * exp(-√(r/ℓ_t))              = (defTUL)
PropT.lean:465/469 PsiT = √(W^{-d} B_{t,0}); sfT = W^{-d/2}(g²+|1-t|)^{-1/2}(r+1)^{-(d-2)/2}e^{-½√(r/ℓ_t)}  = 7_8:23
```
Binder order (read from the pin text of probe lines 68–168; constant `C` is the first `∃` after the listed antecedents):
```
EKSumNdecay      : (no constant)                     ; L | g | m | σ | s t | A
EKSumDecay1      : Prop5Decay d Λ → 3≤d → 2≤n → 0<Λ → ∃C ; L | g | W ε D | s t | m | σ | A
EKSumDecayNAL    : Prop5Decay, Prop5Short d Λ κ, …, 0<κ → ∃C ; same order
EKSumDecay2      : Prop5Decay, Prop5Short, Prop6Diff1 d Λ κ (1/2), … → ∃C ; same order
EKSumDecayNonzero: Prop5Short, Prop8ZeroMode, … → ∃C ; L | g | s t | m | σ | A | 𝒜
EKPropT          : 3≤d → ∃C ; L | g u t | a b
EKTTk            : 3≤d → 2≤n → ∃C ; L | W g t | ℓ Λ | D a | x y
```
Per pin (P = paper display; differences and their delta tag):

| pin | P | hypotheses vs P | conclusion vs P | delta |
|---|---|---|---|---|
| `EKSumNdecay` | (sum_res_Ndecay) | `0≤s≤t<1`, `n≥2`, `‖m‖=1`: = P | `((1-s)/(1-t))^n‖A‖`: = P | none |
| `EKSumDecay1` | (deccA0)+(sum_res_1) | `0≤s≤t≤1-g²/L²`, `W⁻¹≤(1-t)/(1-s)`, `ε∈(0,1)`, `D>1`, (deccA0) as `∃ i j, W^ε ℓ_s ≤ |a_i-a_j|` (= max form): = P; **added** `4 ≤ W^ε`; `g∈(0,Λ]` | `W^{Cε}(ℓ_t²/ℓ_s²)ratio^n‖A‖+W^{-D+C}`, `C=C(d,n,Λ)` indep. of ε,D,L,g,W: = P (uniformity stronger) | T2016b, T2016f |
| `EKSumDecayNAL` | (sum_res_2_NAL) | as above + `∃k, σ k = σ(k+1 mod n)` (= P, cyclic) + `κ ≤ Im m` | `ratio^{n-1}`, no `ℓ_t²/ℓ_s²`: = P | T2016b, T2016f |
| `EKSumDecay2` | (sumAzero)+(sum_res_2) | sum-zero `∀x, Σ_{b: b 0 = x} A b = 0` (= P, index a_1) + **added** `log L ≤ W^ε` + `4 ≤ W^ε` + `κ ≤ Im m` | `ratio^n`: = P | T2016a, T2016b, T2016f |
| `EKSumDecayNonzero` | (sum_res_Ndecay_nonzero) | `1-g²/L² ≤ s ≤ t < 1`, `A ⊇ I_diff` with `I_diff = {i : σ i ≠ σ(i+1)}` (= 3_5:1470) | `≤ C‖𝒜‖` with uniform `C(d,n,Λ,κ)`: **stronger** than P's `≺` | T2016e |
| `EKPropT` | (TTT2) | `0≤u≤t<1`, `(g²/L² ≤ 1-t) ∨ (1-u ≤ g²/L²)` = regimes (i),(ii); `C=C(d)` | `C/(1-u)·𝒯_t(|a-b|)`: = P | T2016c (mixed regime, = P) |
| `EKTTk` | (eq:key_T_reudce) | `1-t ≥ g²/L²`, `k≥2`; `1 ≤ ℓ ≤ Λℓ_t` (P: `0 ≤ ℓ`), `D ⊆ {α: |a-α| ≤ ℓ}` ⊇ P's `D_{≤ℓ}` | `≺` made explicit as `CΛ²`; `(W^dη_t)⁻¹` → `W^{-d}/(1-t)` (`η_t=(1-t)Im m ≤ 1-t`, so not weaker) | T2016d |

Assessment. Restrictions vs P are only (a) `4 ≤ W^ε` and `log L ≤ W^ε` (consequences of "W large" with `L ≤ W^{O(1)}`; P's text absorbs `log L` into `W^{Cε}`, A.2), (b) `ℓ ≥ 1` in `EKTTk`, (c) `κ ≤ Im m` (the paper's standing bulk assumption, already in the merged pins `Prop5Short`/`Prop6Diff1`/`Prop8ZeroMode`). No index range, dimension, window or regime is dropped; constants are ordered before `L, g, W, ε, D, s, t, m` as the ticket requires; no `L^τ` loss; both charges (`EKsgn m σ`, `PropSpin`) are covered. `EKSumDecayNonzero` is a stronger variant (uniform `C` instead of `≺`), declared as T2016e and supported by the numerics below.

## 3. Vacuity, hidden hypotheses, cycles
- No structure fields: the pins are `def … : Prop` whose antecedents are the merged propagator pins (`RBM3D/Propagator/Pins.lean:35–110`), never the old `ThetaDecay*`/`ThetaZeroMode`. `Prop5to8` (structure) is not used.
- No cycle: `ekSumNdecay_holds` ← merged `norm_UN_le`; `ekPropT_holds` ← merged `propT`; `ekTTk_holds` ← merged `key_T_reduce_absorbed`; `ekSumDecay1_two` ← `Prop5Decay` + probe copies of merged `SumDecay.lean` lemmas. No pin takes another EK pin as hypothesis.
- External hypotheses (`Prop5Decay`, `Prop6Diff1`, `Prop8ZeroMode`): limit checks in the prove report (a)(B) to `L=65`, `1-t=g²/L³`; `Prop5Short` is proved (`prop5Short_holds`, used in the instances).
- Satisfiable together: instances in §4 discharge every deterministic hypothesis; far premise of (deccA0) is non-vacuous at the data (`ek_far_point_exists`: `|(2,2,1)|=5 ≥ W^ε ℓ_s = 5`).

## 4. Compiled nonempty instances (probe lines 993–1074; all compiled, axioms standard)
| endpoint | instance | data | open hypotheses (other gates' pins) |
|---|---|---|---|
| `EKSumNdecay` / `ekSumNdecay_holds` | `ekInstNdecay` | d=3, L=5, g=1/2, m=i, σ=(+,−), s=1/2, t=9/10, A=δ₀ | none |
| `EKSumDecay1` / `ekSumDecay1_two` | `ekInstDecay1` | same, W=25, ε=1/2, D=2 (W^ε=5) | `Prop5Decay 3 1` |
| `EKSumDecayNAL` | `ekInstNAL` | σ=(+,+), κ=1/2 | `EKSumDecayNAL`, `Prop5Decay` |
| `EKSumDecay2` | `ekInstDecay2` | σ=(+,−), A=δ₀⊗(δ₀−δ_e), sum-zero proved (`ek_sumZero_Az`), `log 5 ≤ 5` | `EKSumDecay2`, `Prop5Decay`, `Prop6Diff1` |
| `EKSumDecayNonzero` | `ekInstNonzero` | s=.995, t=.999 (P's window needs s ≥ .99), A=univ | `EKSumDecayNonzero`, `Prop8ZeroMode` |
| `EKPropT` / `ekPropT_holds` | `ekInstPropT` | u=1/2, t=9/10, regime (i), a=0, b=e | none |
| `EKTTk` / `ekTTk_holds` | `ekInstTTk` | n=2, W=25, t=9/10, ℓ=Λ=1, D = ℓ¹-ball radius 1 | none |
None degenerate (L=5, n=2, nonzero tensors, nonempty D, open window `s<t<1`).

## 5. Extreme inputs (ticket acceptance; independent script, exact Θ by FFT, d=3, ℓ¹ torus, `S^(B)` of `Defs/Block.lean:38`, m=e^{i·asin(1/2)})
Proved pins (`EKSumNdecay`, `EKPropT`, `EKTTk`, `EKSumDecay1` at n=2) hold at every input by proof. Unproved pins:
```
$ python3 ext.py
(1) EKSumDecayNonzero, n=2: s=1-g^2/L^2, t->1; ||Q^(A) U A|| <= prod_i rowsum(P_i U_i)
 L= 9 g= 0.5 1-t=1.0e-12: rowsum(Proj U(+-))=2.011 rowsum(U(++))=1.004  n=2 alt bound 4.046, same 1.008; trivial ((1-s)/(1-t))^2=9.5e+18
 L=17 g=0.05 1-t=1.0e-12: rowsum(Proj U(+-))=2.002 rowsum(U(++))=1.000  n=2 alt bound 4.008, same 1.000; trivial ((1-s)/(1-t))^2=7.5e+13
 L=33 g= 0.5 1-t=1.0e-12: rowsum(Proj U(+-))=2.013 rowsum(U(++))=1.000  n=2 alt bound 4.053, same 1.001; trivial ((1-s)/(1-t))^2=5.3e+16
 L=33 g=0.05 1-t=1.0e-12: rowsum(Proj U(+-))=2.002 rowsum(U(++))=1.000  n=2 alt bound 4.006, same 1.000; trivial ((1-s)/(1-t))^2=5.3e+12
(2) EKSumDecay2, n=2, sigma=(+,-), A=delta_0 x (delta_0-delta_e), s=0, t=1-g^2/L^2: ||UA||/ratio^2, (1+log L)
 g= 0.5 L= 9: ||UA||/ratio^2=0.1833  1+logL=3.20
 g= 0.5 L=65: ||UA||/ratio^2=0.1701  1+logL=5.17
 g=0.05 L= 9: ||UA||/ratio^2=0.0586  1+logL=3.20
 g=0.05 L=65: ||UA||/ratio^2=0.0452  1+logL=5.17
(3) EKSumDecayNAL n=2 sigma=(+,+): rowsum(U(m^2))^2 / ratio at g->0, t=1-g^2/L^2, s=0
 g=  0.5 L=17: rowsum^2=5.364 ratio=4.983e+00 quotient=1.08e+00
 g= 0.05 L=17: rowsum^2=1.046 ratio=3.996e+02 quotient=2.62e-03
 g=0.005 L=17: rowsum^2=1.000 ratio=3.986e+04 quotient=2.51e-05
```
(1) supports the loss-free strengthening T2016e at `t → 1`, `g → 0`, `L` large (bound ≈ 4 = 2², uniform). (2) one sum-zero tensor, `L → 65`, `g → 0`: bounded (the prover's sup over sum-zero tensors, (a) row 13, grows like `log L`, hence the `log L ≤ W^ε` hypothesis). (3) NAL at `g → 0`: bounded. No counterexample to any pin. Numerics are evidence, not proof (pins are hypotheses until EK-2..5).

## 6. Paper-delta coverage
Every difference in §2 is proposed: `log L ≤ W^ε` (T2016a), `4 ≤ W^ε` (T2016b), `lem:propT` regimes (T2016c), `claim:TTk` `ℓ ≥ 1`, `D`, explicit `Λ²`, `η_t → 1-t` (T2016d), loss-free nonzero-mode bound (T2016e), uniformity in `g ∈ (0,Λ]`, `ℓ¹` distance, sum-zero at index 0 (T2016f). Registry classes of hypothesis Props are given (report (d): `Prop6Diff1` borrowed, the four unproved EK pins owed).

## 7. Ticket items (coverage only)
Items 1 (b5, script), 2 (b6), 3 (b2 + b8 status), 4 ((a)(i)), 5 (b8), 6 (`ekSumDecay1_two`, compiled), 7 (b10, compiled `ek_sumNdecayQ`), 8 (b9: 6 tickets, under 25 vs O2), 9 (b3, compiled). Prove report 265 lines (≤ 300), line 1 `Prover model: claude-sonnet-5-5`.

## 8. Observations (no RETURN)
- O1. The bulk restriction `κ ≤ Im m` in `EKSumDecayNAL`/`EKSumDecay2`/`EKSumDecayNonzero` is not named in a `T2016*` candidate; it is the paper's standing bulk assumption and is already in the merged PT pins. The dispatcher may fold it into T2016f.
- O2. Public helper names in the probe (`ek_*`, `EKuKerQ`) follow the `EK`/`ek` prefix rather than the file stem; the probe stays on the branch, so nothing is merged. EK-1 should make the non-pinned ones `private` or prefix them with the stem (§3 (E)).
- O3. `ek_sumNdecayQ` (item 7 witness) has no instance; it is a supporting lemma, not an endpoint target, and its hypotheses (`‖Q i‖ ≤ 1`, `0 ≤ s ≤ t < 1`) are trivially satisfiable.
- O4. `EKSumDecayNonzero` is a strengthening (uniform `C`) of the paper's `≺`. It is supported numerically but not proved; EK-5 carries the risk. If EK-5 fails, the fallback is the `≺` form (`∀τ>0, … C L^{nτ}`, as in merged `Evolution.lean:629`).

## Verdict
All seven pins, the skeleton and the instances: **PASS**. Overall **PASS** (report-only; probe stays on `t/T2016`). No dispatcher sign-off needed.
