Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 15:01:41 UTC 2026

Notation: `g = ilambda`, `A = g²W^d` (`STAI`), `ρ = (1-s)/(1-tt)`, `P_u(x,y) = STprof_u(x,y) = W^{-d} max(𝒯_u(|x-y|_∞ ∧ L), W^{-D})`, `Q = Q^{(1)} = zeroModeSet {0}`. Sources: `T2339.md`; `DuhamelI.lean` (worktree `t/T2339` = main `3f750b6`); `ZeroModeCalc.lean`; `Step5Pins.lean:290-340,960-990`; `3_5:2251-2283`.

### (i) Exponent table

| # | quantity | value / form | constraint | slack |
|---|---|---|---|---|
| 1 | `𝔠_d` | chosen `1/100` in the `∃ 𝔠d` of `STIngR5` | `ρ³A^{-1/4} ≤ 2A^{3𝔠_d-1/4} ≤ 2A^{-1/5}` (`duhamelI_absorb`, `DuhamelI.lean:725`) needs `3𝔠_d ≤ 1/20` | `1/20-3/100 = 0.02` |
| 2 | `ρ` | `ρ(tt) ≤ ρ(t) ≤ Bctl(t)^{-𝔠_d} ≤ (2A)^{𝔠_d}` | `STConStInd` + window `1/(2A) ≤ W^{-d}B_{t,0} ≤ 2/A`: lower half needs `1-t ≤ g²` (from `1-t ≤ 1-s ≤ g²/L²`), upper half needs `1-t ≥ g²/L^d` (`STReg5II`) | instance `1.6 ≤ 2.307` (below) |
| 3 | `STReg5Mid` from `STReg5II` | `g²/L^d ≤ 1-t` shared; `1-s ≤ g²/L² ≤ g²` | `L² ≥ 1` (`L ≥ 3`, `Sizes.three_le_L`) | factor `L² ≥ 9` |
| 4 | `(TTT2)` regime `hTTT` | `Or.inr : 1-s ≤ g²/L²` | `step5Kernel_profile_explicit_holds` hypothesis for every `v ∈ [s,tt]` since `1-v ≤ 1-s` | `0` at `1-s = g²/L²` (boundary `≤` allowed); instance `0.05 < 0.0625` |
| 5 | equal-sign conjunct (`Q = ∅`, `P = STSigSame`) | `stDuhamelConcl_engine` (`DuhamelI.lean:1884`) with rows 1-4, `hE := ` body of `STEtermsMidConcl` | the drift, martingale and kernel rows of `T2333-prove.md` (a) (i) (rows 4-9) do not depend on the regime beyond rows 2-4 here | as T2333 rows 4-5: drift `0.1233`, `ℰ^{G̃}` `0.29` (exponents of `A`) |
| 6 | mixed conjunct, kernel | **no kernel exponent**: `Q` is applied to the pathwise remainder `R = X - Iv` (route F1 below); `ρ`, `𝔠_d`, drift/martingale rows unchanged from rows 1-2 | none beyond rows 1-4 | no extra `ρ` |
| 7 | averaging constant `C_avg` | `L^{-d} Σ_c 𝒯_u(|c-y|_∞) ≤ C_d/(L^d(1-u)) ≤ e C_d 𝒯_w(r)` for `u ≤ w`, `r ≤ L` | `Σ_c 𝒯_t(|c-b|_∞) ≤ C_d/(1-t)` for all `t<1` (`emn2Exp2_sum_tailT_le`, `EMn2Exp2.lean:262`, private, reachable by `open private`; `DuhamelI` imports it through `EtermsMid`); `(1-u)⁻¹ ≤ (1-w)⁻¹`; `ellT L g w = L` iff `1-w ≤ g²/L²` (`ellT_eq_of_le`, `Defs/Tail.lean:143`) and `exp(-1) ≤ exp(-√(r/ℓ))` for `r ≤ L` (`exp_tail_ge`, `:158`) | `C_d` depends on `d` only; numerics `max ≤ 1.35` (`d=3`, `L ∈ {6,8}`, `g ∈ {.5,1,2}`), `2.13` at `L=4,g=1` (below) |
| 8 | `Q` on the profile | `‖Q R(a)‖ ≤ ‖R(a)‖ + L^{-d} Σ_c ‖R(c,a₁)‖ ≤ N^τ (2 + e C_d) (A^{-1/5} P_{tt}(a) + W^{-D})`, using `L^{-d} Σ_c P_{tt}(c,y) ≤ (1 + e C_d) P_{tt}(x,y)` for all `x,y` | needs `‖R(c,a₁)‖ ≤ N^τ(A^{-1/5}P_{tt}(c,a₁) + W^{-D})` for ALL `c` on the same sample: the label hypotheses of `duhamelI_path` (`hELK`, `hEGt`, `hEEk`, `hMart`, `hRem`) are `∀` labels | constant factor `1 + C_avg e + 1` absorbed in `N^τ` |
| 9 | net lift | `|ξ(u)-ξ(u')| ≤ 2 N^{CH}√|u-u'|` for `ξ = ‖Q LK_u(a)‖` (`Q` averages two label values, each Hölder by `LemDecCalELip_LK2`) | `CH ↦ CH + 1` in `duhamelI_lift` (`:1737`, `A = 2(CH+CR)+6`) | free |
| 10 | ticket's kernel bounds (not used by F1) | `(ThetaBcirc_infint)`: `Σ_b|Θ̊_u(a,b)| ≤ C g⁻²L²`; `(uwp2-92kj00)`: `(1-v)Σ_b|Θ̊_w(a,b)| 𝒯_v(|b-y|) ≤ C 𝒯_w(|a-y|)` | from `prop8ZeroMode_holds` (`Prop5Hold.lean:1266`; `‖m‖=1`, `κ ≤ Im m`, `0<g≤Λ`; `σ₁≠σ₂`: `μ = PropSpin m σ₁·PropSpin m σ₂ = 1`) and `(zdistD+1)⁻¹ ≤ (zdistInf+1)⁻¹`; closure `(1-s) g⁻² L² ≤ 1` is exactly `1-s ≤ g²/L²` | slack `0` (equality allowed); numerics `Σ|Θ̊|g²/L² ≤ 1.17`, `K00 ≤ 1.015`, `(g²+1-u)(|x|₁+1)|Θ̊| ≤ 5.56`, `Σ_x(|x|₁+1)⁻¹/L² ≤ 1.51` for `L ≤ 48` |

Slot bookkeeping (ticket (i)): `Q = zeroModeOp` at `i = 0 : Fin 2` averages over the first coordinate: `(T - Q T)(a) = L^{-d} Σ_c T![c, a 1]` (`wardII_zeroMode`, `WardII.lean:131`). `Q ∘ tensorKer K = tensorKer K[0 ↦ projMat * K 0]` (`zeroModeOp_tensorKer`, `Kernel/Evolution.lean:236`), so slot 0 of `Q∘𝒰_{v,w}` is `(1-L^{-d}J)(α + βΘ) = α(1-L^{-d}J) + βΘ̊` (`projMat_mul_Theta`, `:373`: `projMat * Θ = Theta0`; `Theta0_apply_eq`, `Props4.lean:243`: `Θ̊ = Θ - L^{-d}(1-ξ)⁻¹`) and slot 1 stays `α + βΘ`. `ZeroModeCalc_zeroModeOp_tensorKer_comm` (`ZeroModeCalc.lean:263`, `hK : projMat * K 0 = K 0 * projMat`, discharged by `ZeroModeCalc_projMat_mul_uKer_comm`) gives `Q𝒰 = 𝒰Q`. Confirmed numerically (`d=1`, `L=5`, random circulants; `d=3`, `L=4`) in script 2.

Route F1 (recommended; the ticket's `Q`-version of `Φ` with `|Θ̊|` rows is the fallback and also closes, row 10). Pathwise on the grid sample `X(a) = STgA_K(σ,a)`, `Iv(a) = (Ugen_{s,tt} STgA_0)(a)`: `X - Iv = Dr + Mr + err` with `‖err‖ ≤ 64(1-tt)^{-7}(R+ΔM)` (`pfStep5Grid_duhamel`). The proof of `duhamelI_path` (`:972`) bounds `‖Dr‖+‖Mr‖+err` by `N^τ(A^{-1/5}P_{tt}(a) + W^{-D})` without using `hini` (`hsplit`), at every label. Then `Q X = Q Iv + Q R`, `R = X - Iv`: the first term is the pin's hypothesis (`‖Q Ugen_{s,u}(LK_s)‖ ≤ F`, exactly `STDuhamelConcl` hypothesis form), the second is row 8. `Iv(c,a₁)` for `c ≠ a₀` is NOT controlled by the hypothesis (only `Q Iv` is), so `duhamelI_path` cannot be applied label by label to `X`; a remainder variant `duhamelII_path_rem` (`‖X(a) - Iv(a)‖ ≤ N^τ(A^{-1/5}P_{tt}(a)+W^{-D})`) is needed. `duhamelI_drift` (`:769`), `duhamelI_mart` (`:835`), `duhamelI_section` (`:1419`), `duhamelI_absorb` (`:725`) are `private`: copy under `duhamelII_`; public: `duhamelI_Phi_STprof` (`:516`), `duhamelI_Ugen_le`, `duhamelI_mart_Ugen`, `duhamelI_lift`, `duhamelI_path` (not reusable for the remainder, see above).

DECISIONS §29 (one line each). (1) `0 ≤ s < t ≤ lemT z < 1`: hypotheses of `STIngR5`; instance `t = 31/32 ≤ lemT(zB n)` (`lemT_zB`, `Step34Pins.lean:789`). (2) `1-t ≥ g²/L^d` with `t ≥ 0` forces `g² < L^d`; otherwise `STReg5II` is unsatisfiable (vacuous, no hidden hypothesis). (3) `L`-`W` relation: only `(1-u)⁻¹ ≤ N` as in `duhamelI_htN` (`WO`, `L ≥ 1`); `L^d ≤ W^K` unused. (4) `STReg5II` is `∀ n`; `STConStInd` and all `≺` are `∀ᶠ n`. (5) `STEtermsMidConcl`/conclusion are `Prec` (union inside), sections via `perTimeOfStochDomAt`, union recovered by `duhamelI_lift`, as in T2333. (6) `A ≥ 1`, `Im m ≥ c_κ` eventually from `Admissible`/`|E| ≤ 2-κ` as in T2333. (7) scale `ℓ = L` (`STprof` at `L`); `ellT L g w = L` needs `1-w ≤ g²/L²`, so the mixed engine takes `∀ n, 1 - s n ≤ g²/L²` (NOT the disjunction `hTTT` of `stDuhamelConcl_engine`: with `1-t ≥ g²/L²` the averaging lemma of row 7 has no uniform constant).

### (ii) One concrete nondegenerate instance

`d = 3`, `κ = ε = 𝔡 = 1/10`, `L = 4`, `g = 1` (`szB`, `Step34Pins.lean:710`, at the index with `W = n+4 = 10^12`), `E = Re zB = 1/2`, `s = 19/20`, `t = 31/32`, `𝔠_d = 1/100`, `σ = (+,-)`. External hypotheses: `STEtermsMidConcl` is another gate's pin (proved from `STLWT`, not an assumption of ours); its limit content enters through rows 1-2 and `STConStInd`. Limit computation: `W^{-d}B_{t,0} = W^{-3}·1.49 → 0` while `(1-t)/(1-s) = 5/8` is constant, so `(W^{-3}B_{t,0})^{𝔠_d} → 0 < 5/8 < 1` eventually; at `W = 10^12` it is `0.438`.
```
$ cd .../scratchpad/T2339 && python3 t2339_inst.py     (numpy, no Lean)
Q0 tens(K0,K1)Y == tens(P K0, K1)Y : True
Q0 commutes with tens(K0,K1) (K0 circulant sym): True
T a - Q T a = L^-d sum_c T(c,a1): True
row sums of S =1: True
projMat*Theta == Theta - L^-d (1-u)^-1 : True | row sums Theta =(1-u)^-1: True
Theta*projMat == projMat*Theta (commute): True
0<=s<t<1: True | t<=31/32<=lemT(zB) (Lean lemT_zB): True
regime II: lam^2/L^d=0.01562 <= 1-t=0.03125 <= 1-s=0.05000 <= lam^2/L^2=0.06250 : True
STReg5Mid 1-s<=lam^2: True | hTTT 1-s<=lam^2/L^2: True
A=1.000e+36 rho=1.6000 W^-d B_t0=1.4697e-36 window [1/(2A),2/A]: True
STConStInd: Bctl^cd=0.4382 <= (1-t)/(1-s)=0.6250 < 1 : True
rho<=(2A)^cd: 1.6000 <= 2.3068 : True
lam<=1/dd: True | A>=W^(2dd): True | A<=dd^-2 W^d: True | |E|<=2-kap: True | Im mE=0.9682
rho^3 A^-1/4 = 4.096e-09 <= A^-1/5 = 6.310e-08 : True ; slack exponent 1/20-3cd = 0.020
drift rho A^-1/3 = 1.600e-12, rho A^-1/2 = 1.600e-18  (both <= A^-1/5)
u=0.9688 w=0.9688 ell_w=4.000(=L:True): max_r avg T_u/T_w(r)=1.960 ; avg*L^d*(1-u)=1.001
u=0.9500 w=0.9688 ell_w=4.000(=L:True): max_r avg T_u/T_w(r)=1.542 ; avg*L^d*(1-u)=1.260
u=0.9500 w=0.9500 ell_w=4.000(=L:True): max_r avg T_u/T_w(r)=2.128 ; avg*L^d*(1-u)=1.260
$ cd .../scratchpad/T2339 && python3 t2339_pf.py     (d=3, L in {6,8}, g in {.5,1,2}, 1-u in 6 geometric points of [g²/L³, g²/L²])
{'C8': np.float64(5.5571), 'R1': np.float64(1.1671), 'K00': np.float64(1.0147), 'AVG': np.float64(1.3536), 'AVGZ': np.float64(1.7188), 'RS': np.float64(1.0)}
L 6 sum/L^2 1.2324 / L 8 sum/L^2 1.2931 / L 16 1.4065 / L 32 1.4787 / L 48 1.5063  (sum_x (|x|_1+1)^-1 / L^2)
```
Key: `C8 = max (g²+1-u)(|x|₁+1)|Θ̊_u(x)|`; `R1 = Σ|Θ̊| g²/L²`; `K00 = max (1-u')Σ_b|Θ̊_w(b)|𝒯_{u'}(|z-b|_∞)/𝒯_w(|z|_∞)` over `u' ≤ w`; `AVG = max avg_c 𝒯_{u'}/min_r 𝒯_w(r)`; `AVGZ = max avg·L^d(1-u')`; `RS = max (1-w)L²/g² = 1`. `Θ = (1-uS)⁻¹` by FFT with `S` of `Defs/Block.lean:38-44`. The Lean constants of `prop8ZeroMode_holds` are existential in `(d, Λ, κ)`; the numerics are evidence, not the constants.

### Verdicts

- `stDuhamelII_holds` (Target 1): **PASS**. Equal-sign conjunct: `stDuhamelConcl_engine` with `P = STSigSame`, `hTTT := Or.inr`, `hReg` from rows 3, `hCon` at `𝔠_d = 1/100`, `hE` written out; compiled instance of this conjunct already exists (`DuhamelI.lean:1973`, `(szB, zB, 15/16, 31/32)`). Mixed conjunct: PASS by route F1 (row 6-9); every hypothesis holds together at the instance of (ii); the only new analytic input is the `d`-only constant `C_avg` of row 7.
- `stDuhamelConcl_engineQ1` (Target 2): **PASS** with hypotheses: those of `stDuhamelConcl_engine` except `hTTT`, replaced by `hII : ∀ n, 1 - s n ≤ g²/L²` (row 4, §29 (7)); conclusion `STDuhamelConcl sz {0} P (STflowE z) s t` for any `P` (the argument does not use mixed signs).
- Binding corrections to the ticket route: F1 (no `Θ̊` kernel estimates, no `prop8ZeroMode_holds`, no `Q`-version of `duhamelI_Phi`; instead the remainder variant of `duhamelI_path` and the averaging lemma of row 7); the stage-1b prover may fall back on the ticket route (row 10 closes). Paper-delta candidate `T2339a` (route): the paper takes `Q^{(1)}Θ = Θ̊` with `(ThetaBcirc_infint)`, `(uwp2-92kj00)`; Lean averages the remainder (`3_5:2275`, same statement).

## (a′) Preflight corrections — Thu Oct  8 16:40:22 UTC 2026
No verdict changes. Three statements of (a) differ from the delivered file (evidence in (b)):
1. Target 2 hypotheses: (a) says "those of `stDuhamelConcl_engine` except `hTTT`, replaced by `hII`". The file takes `hReg : STReg5II sz s t` (its second component is `hII`; `duhamelII_reg5II_mid : STReg5II → STReg5Mid`) and has neither `hTTT` nor `hII`; every other hypothesis is that of `stDuhamelConcl_engine`, plus `P`.
2. (a) plans to copy the private helpers of `DuhamelI.lean` under `duhamelII_`; the file reaches ten of them and `emn2Exp2_exists_CR` by `open private` (lines 39-42; precedent `EMn2Exp2.lean:47-54`).
3. (a) row 7 names `emn2Exp2_sum_tailT_le` (`EMn2Exp2.lean:262`); the file uses its `d`-uniform wrapper `emn2Exp2_exists_CR` (`EMn2Exp2.lean:314`), averaging constant `3 C_rad + 1` (`e ≤ 3`, plus 1 for the floor `W^{-D}`).

## (b) Script output (stage 1b rerun, after commit 9457596 on `t/T2339`; worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2339`)
Scratch files `b_*` live under the scratchpad `T2339/`, uncommitted; `docs/...` paths are read in the main worktree.
```
$ date -u; git log --oneline -7; git diff --stat main...t/T2339; wc -l RBM3D/Induction/DuhamelII.lean
Thu Oct  8 16:30:49 UTC 2026
9457596 T2339: DuhamelII, compiled examples at strictly interior data (19/20, 31/32)
2e32b90 T2339: DuhamelII: imports as the ticket's check file (WardII, IniTermII; ZeroModeCalc is transitive)
30a7ef0 T2339: DuhamelII: drop the heartbeat option of duhamelII_section (not needed)
c014c46 T2339: S5-26 Induction/DuhamelII (stDuhamelII_holds, stDuhamelConcl_engineQ1); registry: STDuhamelII no longer owed
7c85567 T2339: DuhamelII section 5 (per-section statement with Q^{(1)})
cf74abe T2339: DuhamelII sections 1-4 (Q^{(1)} on one index, profile average, pathwise remainder, Holder)
3f750b6 Dispatcher V1: DECISIONS §150 (T2297 Amend 1 with the LW engine; S5-26 = T2339; T2338 check fix), H136
 RBM3D/Induction/DuhamelII.lean | 976 +++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean         |   1 -
 2 files changed, 976 insertions(+), 1 deletion(-)
     976 RBM3D/Induction/DuhamelII.lean
[exit 0]
$ lake build RBM3D.Induction.DuhamelII 2>&1 | tail -2; grep -c "DuhamelII.lean" (warnings/errors naming the file)
Note: This linter can be disabled with `set_option linter.style.header false`
Build completed successfully (3892 jobs).
warnings or errors naming DuhamelII.lean: 0
[exit 0]
$ lake env lean RBM3D/Induction/DuhamelII.lean   (elaboration from source: output lines)
output lines:        0
[exit 0]
$ lake env lean ax.lean   (#print axioms of the targets and of the instance)
'RBM.Gauss.Sizes.stDuhamelII_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stDuhamelConcl_engineQ1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.duhamelII_path_rem' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step5Inst.inst_duhamelII_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
[exit 0]
$ grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Induction/DuhamelII.lean
0
$ lake build 2>&1 | grep -E "axiom audit|Build completed|^error|Some required|STDuhamelII"   (worktree, no root import)
error: RBM3D.lean:381:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`, `refutedProps`, `supersededProps`:
  [RBM.Gauss.Sizes.STDuhamelII]
Some required targets logged failures:
error: build failed
[exit 1]
$ lake env lean registry.lean | head -3   (registry.lean = RBM3D.lean with `import RBM3D.Induction.DuhamelII` after its last import)
axiom audit: 10228 theorems, 3037 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
STDuhamelII mentions in the audit ledger output: 0
[exit 0]
$ lake env lean checkeq.lean   (check imports + import RBM3D.Induction.DuhamelII + the equality example)
check-file equality exit: 0
8:import RBM3D.Induction.DuhamelI
9:import RBM3D.Induction.ZeroModeCalc
10:import RBM3D.Induction.WardII
11:import RBM3D.Induction.IniTermII
12:import RBM3D.Induction.DuhamelII
52:example : RBM.Gauss.Sizes.T2339Check.T2339_stDuhamelII_holds := RBM.Gauss.Sizes.stDuhamelII_holds
$ grep -rnE "stDuhamelII_holds|stDuhamelConcl_engineQ1|inst_duhamelII_proved|duhamelII_" RBM3D/ | grep -v "RBM3D/Induction/DuhamelII.lean" | grep -v "/Probe/"
[hits: 0]
$ python3 -I imports.py   (transitive RBM3D imports of the four check imports)
RBM3D.Induction.DuhamelI transitively imported by: []
RBM3D.Induction.ZeroModeCalc transitively imported by: ['RBM3D.Induction.DuhamelI']
RBM3D.Induction.WardII transitively imported by: []
RBM3D.Induction.IniTermII transitively imported by: []
DuhamelI direct imports: ['RBM3D.Induction.EtermsMid', 'RBM3D.Induction.Step5Kernel', 'RBM3D.Induction.PfStep5Grid', 'RBM3D.Path.DifREP3']
RBM3D.Induction.ZeroModeCalc in closure(DuhamelI): True
RBM3D.Induction.WardII in closure(DuhamelI): False
RBM3D.Induction.IniTermII in closure(DuhamelI): False
$ ls .lake/build/lib/lean/RBM3D.olean   (worktree, after the failed full build; Thu Oct  8 16:38:54 UTC 2026)
ls: .lake/build/lib/lean/RBM3D.olean: No such file or directory
$ lake env lean noimp.lean   (the file with the WardII and IniTermII import lines deleted; only `import RBM3D.Induction.DuhamelI` remains)
6:import RBM3D.Induction.DuhamelI
[exit 0] output lines:        0
$ lake env lean ex_ax.lean   (the three examples of the instance section, renamed b_ex1..3, and inst_duhamelII_proved: #print axioms)
'b_inst_duhamelII_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'b_ex1' depends on axioms: [propext, Classical.choice, Quot.sound]
'b_ex2' depends on axioms: [propext, Classical.choice, Quot.sound]
'b_ex3' depends on axioms: [propext, Classical.choice, Quot.sound]
[exit 0]
$ python3 -I prov.py   (adaptation of the in-repo sources; comments stripped for the counts)
DuhamelI.lean:972-1150 (179 lines) -> DuhamelII.lean:216-393 (178 lines): diff +17 -18
DuhamelI.lean:1419-1695 (277 lines) -> DuhamelII.lean:497-843 (347 lines): diff +105 -35
code-level counts (comments stripped): prop8ZeroMode 0, Theta0 0, ZeroModeCalc 0, ThetaBcirc 0, stWardII 0, stIniTermII 0
grep -c 'RBM1D\|RBM2D' in the file: 0
$ git diff main...t/T2339 -- RBM3D/Test/Axioms.lean | grep "^[-+] "
-   `RBM.Gauss.Sizes.STDuhamelII, -- integrated hierarchy with `Q^{(1)}`, case (ii); S5-01 (T2138, DECISIONS §40: owed)
$ git diff --stat 3f750b6 main -- RBM3D/Test/Axioms.lean RBM3D.lean   (main since the worktree base)
 RBM3D.lean | 1 +
 1 file changed, 1 insertion(+)
```

Statements and instances, extracted by script (`stmts.py`):
```
$ sed -n 327,329p RBM3D/Induction/Step5Pins.lean   (the pin)
def STDuhamelII (d : ℕ) : Prop :=
  STIngR5 d STReg5II (fun sz E s t => STEtermsMidConcl sz E s t →
    STDuhamelConcl sz {0} STSigMixed E s t ∧ STDuhamelConcl sz ∅ STSigSame E s t)
$ grep -n "def T2339_stDuhamelII_holds" docs/tickets/checks/T2339-check.lean   (the check statement)
44:def T2339_stDuhamelII_holds : Prop := ∀ d : ℕ, STDuhamelII d
$ python3 -I stmts.py holds   (the target, whole theorem)
theorem stDuhamelII_holds (d : ℕ) : STDuhamelII d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs hst htz hReg _ _ _ _ _ hCon _ _ _ _ hE
  exact ⟨stDuhamelConcl_engineQ1 hd hκ hε h𝔡 sz hflow hs hst htz hReg hCon hE STSigMixed,
    stDuhamelConcl_engine hd hκ hε h𝔡 sz hflow hs hst htz (duhamelII_reg5II_mid hReg)
      (fun n => Or.inr (hReg n).2) hCon hE STSigSame⟩
$ python3 -I stmts.py engine   (the public engine, signature without docstring)
theorem stDuhamelConcl_engineQ1 (hd : 3 ≤ d) {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (sz : Sizes d)
    {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (htz : ∀ n, t n ≤ lemT (z n)) (hReg : STReg5II sz s t)
    (hCon : STConStInd sz (1 / 100) s t)
    (hE : ∀ D : ℝ, 0 < D →
      sz.Prec (U := STIdx2 sz s t) (fun n p ω => ‖STELKLK sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => (STAI sz n) ^ (-(1 / 3) : ℝ) * (etaT (STflowE z n) (p.1 : ℝ))⁻¹ *
          STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)) ∧
      sz.Prec (U := STIdx2 sz s t) (fun n p ω => ‖STEGt sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => (STAI sz n) ^ (-(1 / 2) : ℝ) * (etaT (STflowE z n) (p.1 : ℝ))⁻¹ *
          STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)) ∧
      sz.Prec (U := fun n => STIdx2 sz s t n × Fin 2)
        (fun n p ω => ‖STEEk sz n (STflowE z n) (p.1.1 : ℝ) p.2 p.1.2.1 p.1.2.2 ω‖)
        (fun n p _ => (STAI sz n) ^ (-(1 / 2) : ℝ) * (etaT (STflowE z n) (p.1.1 : ℝ))⁻¹ *
          STprof sz n (p.1.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.1.2.2 0) (p.1.2.2 1) ^ 2))
    (P : (Fin 2 → Bool) → Prop) :
    STDuhamelConcl sz {0} P (STflowE z) s t := by
$ python3 -I stmts.py inst   (section "Compiled nonempty instances", docstrings stripped)
namespace RBM.Gauss.Step5Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst RBM.Path Filter

theorem inst_duhamelII_proved (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STEtermsMidConcl sz E s t →
      STDuhamelConcl sz {0} STSigMixed E s t ∧ STDuhamelConcl sz ∅ STSigSame E s t) szB zB
      (fun _ => 15 / 16) (fun _ => 31 / 32) Cd :=
  inst_duhamelII (stDuhamelII_holds 3) Cd hCd

example (hE : STEtermsMidConcl szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32)) :
    STDuhamelConcl szB {0} STSigMixed (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  stDuhamelConcl_engineQ1 (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10)
    (by norm_num : (0 : ℝ) < 1 / 10) szB flow_zB (fun _ => by norm_num) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) szB_reg5II
    (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) (by norm_num)) hE STSigMixed

example (hE : STEtermsMidConcl szB (STflowE zB) (fun _ => 19 / 20) (fun _ => 31 / 32)) :
    STDuhamelConcl szB {0} STSigMixed (STflowE zB) (fun _ => 19 / 20) (fun _ => 31 / 32) :=
  stDuhamelConcl_engineQ1 (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10)
    (by norm_num : (0 : ℝ) < 1 / 10) szB flow_zB (fun _ => by norm_num) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) (fun n => ⟨by simp [szB]; norm_num, by simp [szB]; norm_num⟩)
    (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) (by norm_num)) hE STSigMixed

example (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STEtermsMidConcl sz E s t →
      STDuhamelConcl sz {0} STSigMixed E s t ∧ STDuhamelConcl sz ∅ STSigSame E s t) szB zB
      (fun _ => 19 / 20) (fun _ => 31 / 32) Cd :=
  inst_ing5 STReg5II _ (stDuhamelII_holds 3) szB zB flow_zB (fun _ => 19 / 20) (fun _ => 31 / 32)
    (fun _ => by norm_num) (fun _ => by norm_num) (szB_flow_ht (by norm_num))
    (fun n => ⟨by simp [szB]; norm_num, by simp [szB]; norm_num⟩)
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠) Cd hCd

end RBM.Gauss.Step5Inst
```

Narrative (facts from the listings above and the files):
1. Both targets are proved in `RBM3D/Induction/DuhamelII.lean` (976 lines; stop rule 1900 not reached; sections 1-6 start at lines 53, 102, 203, 396, 448, 846; instances 935-976). `stDuhamelII_holds` is unconditional: three standard axioms, check-file equality example compiles (exit 0). Commits cf74abe..2e32b90 are from the previous attempt (the state file records a usage-limit stop); 9457596 (the interior examples) is the only commit of this attempt.
2. The pin: `𝔠_d = 1/100` in the `∃`; the mixed conjunct is `stDuhamelConcl_engineQ1`; the equal-sign conjunct is `stDuhamelConcl_engine` with `Q = ∅`, `hReg` from `duhamelII_reg5II_mid` (`1-s ≤ g²/L² ≤ g²`), `hTTT := fun n => Or.inr (hReg n).2`. The nine Step 1-4 premises of `STIngR5` and `Cd` are not used (five `_`, four `_`, `Cd` in the proof above; as `T2333c`).
3. Route F1 of (a), no `Θ̊` kernel estimate: `Q^{(1)}` is applied to the pathwise remainder `R = (𝓛-𝒦)_{tt} - 𝒰_{s,tt}(𝓛-𝒦)_s`. `duhamelII_path_rem` bounds `R` at every label of one grid sample and `duhamelII_section` evaluates it at `(σ, a)` and at `(σ, (c, a₂))` for all `c`; `duhamelII_Q_sub_le`: `‖QX_a - QI_a‖ ≤ ‖X_a - I_a‖ + L^{-d} Σ_c ‖X_(c,a₂) - I_(c,a₂)‖`; `duhamelII_prof_avg`: `L^{-d} Σ_c P_u(c,y) ≤ (3 C_rad + 1) P_u(x,y)` for `1-u ≤ g²/L²` (radial sum `emn2Exp2_exists_CR`; zero mode of `𝒯_u` by `exp_tail_ge`, `ℓ_u = L`). The initial term `Q^{(1)}𝒰_{s,tt}(𝓛-𝒦)_s` is the hypothesis `hini` (event by `ST_grid_whp_zero`); the closure is `duhamelII_close` (`duhamelI_absorb` at the floor `2W^{-D}`); the lift to all `u ∈ [s,t]` is `duhamelI_lift` with `duhamelII_holder` (`LemDecCalELip_LK_sub`, constant `N^{12}`). Code-level counts of `prop8ZeroMode`, `Theta0`, `ZeroModeCalc`, `ThetaBcirc` in the file: 0 (prov.py line).
4. The engine takes `STReg5II`, not `STReg5Mid` with the disjunction `hTTT` of `stDuhamelConcl_engine`: `duhamelII_prof_avg` needs `1-t ≤ g²/L²` for a uniform constant ((a) §29 (7)).
5. Provenance: `duhamelII_path_rem` and `duhamelII_section` are in-repo adaptations of `duhamelI_path` and `duhamelI_section` (prov.py: diff +17 -18 of 179 lines; +105 -35 of 277). Ten private helpers of `DuhamelI.lean` and `emn2Exp2_exists_CR` are reached by `open private` (lines 39-42), not copied: this deviates from the ticket's "copy private helpers under `duhamelII_`" (precedent `EMn2Exp2.lean:47-54`). Nothing is ported from RBM1D or RBM2D: this stage's tool log has no access to either, and the file mentions neither (count 0); no diff-stat.
6. Hygiene: `sorry|admit|native_decide|^axiom` count 0; one `set_option maxHeartbeats 1000000 in` (line 209, reason comment line 210; `DuhamelI.lean` has two, lines 965 and 1413); `lake build` prints no line naming the file; elaboration from source prints nothing. Public names: `duhamelII_path_rem`, `stDuhamelConcl_engineQ1`, `stDuhamelII_holds`, `inst_duhamelII_proved`; every other helper is `private` with the `duhamelII_` prefix.
7. Registry: one deleted line, the owed line `STDuhamelII`; `Test/Axioms.lean` is unchanged on `main` since the worktree base `3f750b6`. The worktree's full `lake build` stops at the root audit naming `STDuhamelII`, as it must once the owed line is deleted and `RBM3D.lean` (the hub's file) lacks the import. `registry.lean` (`RBM3D.lean` with the import after its last import line, uncommitted scratch) runs the whole-library `#assert_rbm_axioms`: exit 0, 10228 theorems, 0 axioms, 0 mentions of `STDuhamelII`. The literal pre-check (`import RBM3D`) cannot run here: `RBM3D.olean` is absent after the failed `lake build` (`ls` line above). I did not edit `RBM3D.lean`, not even temporarily.
8. Imports: `DuhamelI`, `WardII`, `IniTermII`, i.e. the check's four minus `ZeroModeCalc`, which is transitive through `DuhamelI` (imports.py). `WardII` and `IniTermII` are unused (noimp.lean elaborates, exit 0) but kept, as the ticket says "exactly as the check, dropping what is transitive".
9. Instances: `inst_duhamelII_proved` (the ticket's pattern); `stDuhamelConcl_engineQ1` at the pin data `(szB, zB, 15/16, 31/32)` (`1-s = g²/L² = 1/16`, the closed end of the regime) and at strictly interior data `(19/20, 31/32)` (`1/64 ≤ 1/32 ≤ 1/20 < 1/16`, the `s` of (a)(ii)); the pin at the interior data by `inst_ing5`. Every deterministic hypothesis is discharged; `hE` (the body of `STEtermsMidConcl`, whose proof needs `STLWT`) stays a hypothesis of the two engine examples. All four depend only on the three standard axioms (ex_ax.lean).

## (c) Verified Mathlib names (every identifier of the file resolved by script `names.lean` against the environment of the built module; 101 library names, tactics and keywords removed)
```
Classical.not_not ENNReal.ofReal Filter.eventually_ge_atTop Finset.card_univ Finset.measurable_sum Finset.mem_range Finset.mul_sum Finset.range Finset.sum_add_distrib Finset.sum_congr
Finset.sum_const Finset.sum_le_sum Finset.sum_sub_distrib Finset.sup_le Finset.toList_singleton Fintype.card_fin Fintype.card_prod Function.update Function.update_of_ne Function.update_self
MeasurableSet.iUnion MeasureTheory.ae_all_iff MeasureTheory.ae_iff MeasureTheory.measure_mono Nat.cast_nonneg Nat.le_ceil Nat.lt_succ_of_le Nat.one_le_iff_ne_zero Nat.pos_of_ne_zero
Nat.zero_le Or.inr Real.exp_add Real.exp_one_lt_d9 Real.exp_pos Real.one_le_rpow Real.rpow_add Real.rpow_le_rpow_of_exponent_le Real.rpow_le_rpow_of_nonpos Real.rpow_mul Real.rpow_natCast
Real.rpow_neg Real.rpow_nonneg Real.rpow_one Real.rpow_pos_of_pos Real.sqrt_eq_rpow Real.sqrt_nonneg Set.mem_compl_iff Set.mem_iUnion Set.mem_union abs_norm_sub_norm_le abs_of_pos absurd
add_assoc add_le_add add_nonneg div_le_div_of_nonneg_right div_le_self div_nonneg half_pos inv_anti₀ inv_nonneg inv_pos le_add_of_nonneg_left le_add_of_nonneg_right le_antisymm le_div_iff₀
le_max_left le_max_right le_of_eq le_rfl le_trans lt_of_le_of_lt lt_of_lt_of_le max_le measurableSet_lt measurable_const mul_assoc mul_comm mul_inv mul_le_mul mul_le_mul_of_nonneg_left
mul_le_mul_of_nonneg_right mul_nonneg mul_pos neg_nonpos norm_add_le norm_le_insert' norm_mul norm_nonneg norm_sub_le norm_sum_le not_le not_lt not_or nsmul_eq_mul one_div
one_div_le_one_div_of_le one_le_pow₀ pow_ne_zero sq_nonneg sub_nonneg
```
No deprecation warning in the build log (count of lines naming the file: 0). Verified absent: none checked in this stage.

## (d) Open issues and paper-delta candidates
- Hub, at merge: add `import RBM3D.Induction.DuhamelII` after the last `import` line of `RBM3D.lean` (line 378 at the worktree base, before `#assert_rbm_axioms`); the worktree `lake build` fails until then (above), the scratch root run passes (exit 0). The registry edit applies cleanly: of the two registry files, `main` changed only `RBM3D.lean` since `3f750b6` (diff-stat above).
- `T2339a` (route, not a statement): the paper takes `Q^{(1)}Θ = Θ̊` with `(ThetaBcirc_infint)` and `(uwp2-92kj00)` (`3_5:2263-2277`); Lean applies `Q^{(1)}` to the pathwise remainder and averages its profile over the first index (same conclusion, `3_5:2275`). Proposal: one line in `docs/paper-deltas.md`, next to `T2134g`.
- `T2339b` (sign class): `stDuhamelConcl_engineQ1` has no sign hypothesis (any `P`); the paper uses `Q^{(1)}` only for `σ₁ ≠ σ₂`. The remainder route uses no sign property; the `Q^{(1)}`-form for equal signs is a by-product that the pin does not use.
- `T2339c` (pin shape): as `T2333c`, `STDuhamelII` carries nine Step 1-4 premises and `Cd` that its proof does not use (item 2); the dispatcher may restate the pin without them.
- Imports: `WardII` and `IniTermII` are unused (item 8); the dispatcher may drop them at the next amendment.
- Downstream (`#check` in the equality run): `ST_step5_caseII_of_pins : STEtermsMid d → STDuhamelII d → STIniTermII d → STWardII d → STStep5II d`; `stWardII_holds` and `stIniTermII_holds` resolve there. With `stDuhamelII_holds`, `STStep5II` waits only for `STEtermsMid` (`STLWT`, the ticket's "Not targets").
- Public API for reuse: `stDuhamelConcl_engineQ1` (any sign class, `Q = {0}`) and `duhamelII_path_rem` (the remainder form of `duhamelI_path`, no initial term).
