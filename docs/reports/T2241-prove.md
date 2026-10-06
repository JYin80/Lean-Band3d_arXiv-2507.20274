Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 01:58 UTC 2026

Scripts (python3, numpy; no Lean) in `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2241/`: `ba.py` (solver of `(self_m)`, `m = L^{-d} tr(λΨ^{(B)} - z - m)^{-1}`, `1_2:626-629`, Newton continuation from `Im z = 10`; `Ψ^{(B)}` built from `zdistD(a-b) = 1`, `Defs/Lattice.lean:108`), `run1.py`..`run4.py`.

### (i) Exponent table and pin table

| quantity | value | constraint | slack |
|---|---|---|---|
| `(𝔠, 𝔡)` | `(1/6, 1/10)` | `Admissible` at `sz0` (`SizesInst`, `L=4(n+1)`, `W=(2(n+1))^5`, `λ=(2(n+1))^{-6}`) and at `S0 = clsSz 4 g0` (`λ = g0`, `0 < g0 ≤ 10`) | `W^{-d/2+𝔡} = (2(n+1))^{-7}` vs `λ_n = (2(n+1))^{-6}` at `sz0`; `λ ≤ 𝔡⁻¹ = 10` |
| `κ`, `E` | `0.05`, `E = 0` (`L = 4`, `d = 3`) | `ρ_N(E) ≥ κ` | `ρ_N(0) = 0.2636` (`λ=0.3`), `0.1781` (`λ=10`): ratios `5.27`, `3.56` |
| `δ` (window) | `{0.025, 0.05}` | `ρ_N(x) ≥ κ/2 = 0.025` on `|x-E| ≤ δ` | min `ρ_N` on window `0.2635` / `0.1779`: ratios `10.5` / `7.1` |
| `UNDens'` constants `c, K, Lp` | `c ≤ 0.2511`, `K ≥ 0.8282`, `Lp ≥ 0.500` (grid estimate, `η ≤ 1`); `UNDens` part (`η ≤ 10`): `0.0417 ≤ Im m ≤ 0.8282` | `0<c`, `K`, `Lp` fixed before `∀ᶠ n`, uniform in `n` | `c` is not `πκ = 0.157` (as T2173); `c` positive on the whole box |
| `CV₀` (`UNMeanBound`) | `1/2` (instance); the row `UNNormBARow` gives `CV₀`, the assembly uses `CV₀+1 ≥ 1` | `2d|λ_n| ≤ N^{CV₀}` eventually (`|eig(λΨ)| ≤ 2dλ`) | `n=0`: `N_0^{1/2} = 1448.2` vs `2d𝔡⁻¹ = 60`: factor `24.1`; `n₀ = 0` along `sz0` and `S0`. For tiny `CV₀ = 0.01`, `n₀` would need `N ≥ 6.5e177`: `unMeanBound_ba` is an eventual statement for each `CV₀ > 0`, instances use `CV₀ ≥ 1/2` |
| `τ_s` | `1/100` | `0<τ_s<1`, `τ_s ≤ 𝔠𝔡 = 1/60` (`UNStep1GoodC''`); `τ_s < 8/11 = 0.7273` (T2208c, supervisor 1955 B2) | factors `1.667` and `72.7` |
| `t*_n = N^{-1+τ_s}` | `t*_0 = 5.516e-07` | `0 ≤ s_n ≤ 1` for `lamHat` | `t* ≤ 1` for all `n` since `N ≥ 1`, `τ_s < 1` |
| `(eq:WO)` at `𝔡' = 𝔡/2 = 1/20` for `λ̂ = λ e^{t*/2}` (`admissible_lamHat`) | upper `λ̂ ≤ 𝔡'⁻¹ = 20`; lower `W^{-d/2+𝔡'} ≤ λ̂` | upper: `λ e^{s/2} ≤ 𝔡⁻¹ e^{1/2} ≤ 2𝔡⁻¹` since `e^{1/2} = 1.6487 ≤ 2`; lower: `W^{-d/2+𝔡/2} ≤ W^{-d/2+𝔡} ≤ λ ≤ λ̂` (`W ≥ 1`) | script (run3): `min (1/𝔡')/λ̂ = 1280` (`sz0`), `66.7` (`S0`); `min λ̂ / W^{-d/2+𝔡'} = 2.38` (`sz0`), `45.7` (`S0`), `n < 2000`; `SizeTendsto`, `Bandwidth` unchanged by `withLam` |
| shift constant `C` of `UNTrLocalInit'` | `C_max = max |a⁻¹ m(z/a; λ/a) - m(z; λ)| / t* = 0.2968` (`a = e^{-t*/2}`, `z = i η`, `η ∈ {1e-3, 0.1, 1}`, `t* ∈ {1e-2,1e-3,1e-4}`) | tolerance `W^τ (Bctl(1-η) + t*) ≥ t*` since `W^τ ≥ 1`; need `C t* ≤ W^τ t*` (even without `Bctl`) | factor `1/C_max = 3.37`; `(2 C_max)^{1/τ} < 1` for `τ ∈ {0.1, 0.05, 0.01}`, so no `W₀` is needed |
| window bridge `Im z/a ∈ (1, 1/a]` | `1/a - 1 = 0.5013 t*` (`t* = 1e-2`), `0.5000 t*` (`1e-4`) | `|s(z') - s(z'')| ≤ |z'-z''|` for `Im ≥ 1` (`η`-Lipschitz bridge) | absorbed in `t*` (factor `2`) |
| `Bctl(1-η)` at `(d, L) = (3, 4)` | `W^{-3}[(λ²+η)^{-1} + (4^3 η)^{-1}]` (`Bparam K=0`, `|1-t| = η`) | `UNTrLocalInit'` tolerance | `W=32, τ=0.05, t*=1e-3`: `shift/tol ∈ [0.035, 0.195]`; `W=2`: `≤ 0.010` |

Pin table (targets 1-4; class per ticket registry paragraph; consumer per ticket "Consumers"):

| pin | content | paper | class | consumer |
|---|---|---|---|---|
| `UNModelC.ba`, `ba_spec` | `UNModel.ba` plus mean `λΨ` (Hermitian) | `1_2:611-616` | proved (`rfl`) | `UNCoreC''` at `M = UNModelC.ba sz` |
| `UNKind.ba` | `lamV = 0`, bulk `BAbulk`, `mdet = BAm` | `1_2:624-629` | proved (def) | `un_claimAll_of_rowsk`, `UNOUQUEk_zero_of_UNQuek` |
| `UNQueBA`, `UNLocAvgBA` | `UNQuek`, `UNLocAvgk` at the BA kind | `1_2:655` | owed (BA-M3 via `UNQueBA_of_BAEnd_QUEL`; BA-M1) | `baBUniv_of_rows` |
| `UNMLOutBA d` | main-induction outputs on the T2197 carrier | `1_2:686` | owed (BA-V3) | `un_claimAll_of_rowsBA` |
| `UNOURowBA`, `UNEMCTE2RowBA`, `UNJakUywRowBA`, `UNClaimRowBA` | model-generic UN rows at `UNKind.ba` | `1_2:566-581` | owed (UN rows) | `un_claimAll_of_rowsBA` |
| `UNDensBARow'` | `UNDens'` of `m(·, λ_n)`, `ρ = BArho`, `∃ δ₀ ∀ δ ≤ δ₀`, bulk stability `κ/2` | `1_2:626-629` | owed (BA-C2) | `UNCoreC''` |
| `UNTrLocalBARow`, `UNTrLocalInitBARow'` | `UNTrLocal` / `UNTrLocalInit'` of the BA model at `m(·, λ_n)` | `1_2:655` (local laws) | owed (BA-N1) | `UNCoreC''` |
| `UNNormBARow` + `unMeanBound_ba` | `∃ CV₀` norm bound; `UNMeanBound` of `λΨ` | `1_2:611` | owed (BA-N1); `UNMeanBound` proved here (structural) | `UNCoreC''` conjunct |
| `BAEnd_QUEL` | `(Meq:QUE)`, `(Meq:QUE2)` at law `seqP (sz.withLam 0)`, bound `queBound` | `1_2:655` | owed (BA-M3) | MA-06, `UNQueBA_of_BAEnd_QUEL` |
| `BAEnd_BUnivL` | `UNUnivDilAt (UNModel.ba sz) (BArho …)` | `1_2:452-460, 655` | concluded by `baBUniv_of_rows` | MA-06 |
| `baBUniv_of_rows` | `UNCoreC''` + rows `→ BAEnd_BUnivL` | `1_2:566-581` | proved here | BA-N2 |

Refuted-pin check on the check file (`UNStep1Good, UNInfty1Row, UNStep1GoodC, UNCoreC, UNTrLocalInit, UNStep1GoodC', UNCoreC'`; PCRE with no trailing `'`/word char):
```
$ grep -cP "(?<![\w'])(UNStep1Good|UNInfty1Row|UNStep1GoodC|UNCoreC|UNTrLocalInit|UNStep1GoodC'|UNCoreC')(?![\w'])" docs/tickets/checks/T2241-check.lean
1
$ (same, lines not starting with a comment opener)    -> no output
```
The single hit is in the header comment; no declaration or hypothesis uses a refuted pin (the primed `UNTrLocalInit'`, `UNCoreC''` are the merged successors, `PinsC2.lean:72, :106`).

### (ii) One concrete nondegenerate instance (`d = 3`, `L = 4`, `W ∈ {2, 32}`, `λ ∈ {0.3, 10}`, `κ = 0.05`, `E = 0`)
`m` does not depend on `W`; `W` enters only `N = (WL)^3` (`512` at `W=2`, `2097152` at `W=32`) and the tolerance. `S0 = clsSz 4 g0` uses the `Classical`-chosen `fp 4 _`, so its `g0` is not computable here; `λ = 0.3` stands for the class `(L, g) = (4, 3/10)` of T2173.

```
$ cd <scratchpad>/T2241 && python3 run1.py && python3 run4.py
Psi_B rows sum: 6.0 6.0 max eig 5.999999999999998 min eig -6.000000000000003 =2d: 6
lam=0.3: m(0+i1e-9)=0.00000+0.82816j rho_N(0)=0.2636 residual=1.1e-16 kappa=0.05 ok=True
lam=10.0: m(0+i1e-9)=0.00000+0.55938j rho_N(0)=0.1781 residual=1.1e-16 kappa=0.05 ok=True
 lam=0.3 delta=0.025: eta<=10: min Im m=0.0985 max Im m=0.8282; eta<=1: min Im m=0.5490 max|m|=0.8282; complex Lip(grid)=0.358; Lip_x(Im m)=0.0044
 lam=0.3 delta=0.05: eta<=10: min Im m=0.0985 max Im m=0.8282; eta<=1: min Im m=0.5489 max|m|=0.8282; complex Lip(grid)=0.358; Lip_x(Im m)=0.0089
 lam=10.0 delta=0.025: eta<=10: min Im m=0.0417 max Im m=0.5594; eta<=1: min Im m=0.2513 max|m|=0.5594; complex Lip(grid)=0.499; Lip_x(Im m)=0.0106
 lam=10.0 delta=0.05: eta<=10: min Im m=0.0417 max Im m=0.5594; eta<=1: min Im m=0.2511 max|m|=0.5594; complex Lip(grid)=0.500; Lip_x(Im m)=0.0213
lam=0.3 delta=0.025: min rho_N(x)=0.2636 >= kappa/2=0.025: True; max Lip_x(rho)=0.0014
lam=0.3 delta=0.05: min rho_N(x)=0.2635 >= kappa/2=0.025: True; max Lip_x(rho)=0.0028
lam=10.0 delta=0.025: min rho_N(x)=0.1780 >= kappa/2=0.025: True; max Lip_x(rho)=0.0034
lam=10.0 delta=0.05: min rho_N(x)=0.1779 >= kappa/2=0.025: True; max Lip_x(rho)=0.0068
```
(grid: 21 `x`-points, 32 `η` log-points in `[1e-6, 10]` plus `η = 1, 10`; Lipschitz constants are grid lower estimates; `ρ` at `η = 1e-9`.) `UNDens'` (box `|Re z - E| ≤ δ`, `0 < Im z ≤ 1`) and `UNDens` (`η ≤ 10`): `Im m` bounded below by `0.0417` and above by `0.8282`, bulk stability holds: `UNDensBARow'` is satisfiable at these data.

```
$ python3 run2.py        (shift S = |a^-1 m(z/a; lam/a) - m(z; lam)|, a = exp(-t*/2), L=4, d=3, E=0)
 lam=0.3 eta=0.001 | t*=0.01: S=2.968e-03 S/t*=0.2968 | t*=0.001: S=2.966e-04 S/t*=0.2966 | t*=0.0001: S=2.966e-05 S/t*=0.2966
 lam=0.3 eta=0.1 | t*=0.01: S=2.701e-03 S/t*=0.2701 | t*=0.001: S=2.700e-04 S/t*=0.2700 | t*=0.0001: S=2.700e-05 S/t*=0.2700
 lam=0.3 eta=1 | t*=0.01: S=1.156e-03 S/t*=0.1156 | t*=0.001: S=1.157e-04 S/t*=0.1157 | t*=0.0001: S=1.158e-05 S/t*=0.1158
 lam=10.0 eta=0.001 | t*=0.01: S=2.795e-03 S/t*=0.2795 | t*=0.001: S=2.789e-04 S/t*=0.2789 | t*=0.0001: S=2.788e-05 S/t*=0.2788
 lam=10.0 eta=0.1 | t*=0.01: S=2.331e-03 S/t*=0.2331 | t*=0.001: S=2.327e-04 S/t*=0.2327 | t*=0.0001: S=2.327e-05 S/t*=0.2327
 lam=10.0 eta=1 | t*=0.01: S=4.151e-04 S/t*=0.0415 | t*=0.001: S=4.158e-05 S/t*=0.0416 | t*=0.0001: S=4.159e-06 S/t*=0.0416
C_max = max S/t* = 0.2968
 W=32 tau=0.05 lam=0.3 eta=0.001 t*=1e-3: Bctl=8.122e-04 tol=2.155e-03 shift/tol=0.138
 W=32 tau=0.05 lam=10.0 eta=0.1 t*=1e-3: Bctl=5.073e-06 tol=1.195e-03 shift/tol=0.195
 W=2 tau=0.05 lam=10.0 eta=0.1 t*=1e-3: Bctl=2.078e-02 tol=2.255e-02 shift/tol=0.010
tau=0.1: W0=(2*C_max)^(1/tau) such that C_max t* <= W^tau t*/2 : 5.436e-03
t*=0.01: 1/a-1=5.0125e-03 ratio to t*=0.5013
```
Reading: `S/t*` is stable under `t* → t*/100` (a derivative, not noise), so `|a⁻¹m(z/a; λ/a) - m(z; λ)| ≤ C t*` with `C = 0.30`; `UNTrLocalInit'` is the BA local law at coupling `λe^{t*/2}` (`a⁻¹·ouInit = (λ/a)Ψ + V`, `ouInit = λΨ + aV` from `PinsK.lean:75`) plus a shift below the `t*` term of the tolerance. The full output has `W ∈ {2, 32}`, `τ ∈ {0.05, 0.1}` rows (all `shift/tol ≤ 0.195`).

```
$ python3 run3.py        (merged `split`: block = (i.val / W) mod L, offset = i.val % W; d=3, L=4, W=2)
d=3 L=4 W=2: N=512=(WL)^d=512; #{y: PsiI x y != 0} min=6 max=6 (2d=6); symmetric=True
  max|eig(Psi)|=6.000000 (<= row sum 2d=6)
  lam=0.3: max|eig(lam Psi)|=1.8000 = 2d*lam=1.7999999999999998
  lam=10.0: max|eig(lam Psi)|=60.0000 = 2d*lam=60.0
  sz0: N_0=2097152, 2d*lam_0=0.09375 <= N_0^(1/2)=1448.2; first n0=0; 2d/dd=60.0
  S0(lam=0.3): N_0=2097152, 2d*lam_0=1.8 <= N_0^(1/2)=1448.2; first n0=0; 2d/dd=60.0
  admissible_lamHat sz0: WO(dd/2=0.05) holds n<2000: True; min (1/dd')/lamhat=1280.000; min lamhat/W^(-d/2+dd')=2.38; e^(1/2)=1.6487 <= 2
  admissible_lamHat S0(lam=0.3): WO(dd/2=0.05) holds n<2000: True; min (1/dd')/lamhat=66.667; min lamhat/W^(-d/2+dd')=45.7; e^(1/2)=1.6487 <= 2
```
`unMeanBound_ba` route checked: row sum of `Ψ` is `2d` at every row (`RBM.card_adj`, `Neighbours.lean:168`, `L ≥ 3`), the eigenvalue bound `|eig| ≤ R` is attained (`6.000000`), so the bound `2d|λ|` is sharp and `UNPins_eig_le_rowsum` needs no loss.

### §29 (1)-(7) (from the ticket text, rechecked against the merged pins above)
(1) times: `UNMLOutBA` `0 ≤ t_n ≤ t₀_n`; OU times `0 ≤ t ≤ t* = N^{-1+τ_s}` (`t*_0 = 5.5e-07`); `lamHat` at `0 ≤ s_n ≤ 1` (checked). (2) no gate. (3) no `L`-`W` relation beyond `Admissible`. (4) bulk premises `∀ᶠ n BAbulk`; `BAFlow` has `∀ n`. (5) `∃ z` inside the probability (`UNTrLocal`, `UNTrLocalInit'`: `PinsC2.lean:72`); block/set unions inside `BAEnd_QUEL` per `a`, `A`. (6) `0 < κ, ε, 𝔡, τ, D, CV₀` premises (instance: all positive above). (7) scales those of `UNCoreC''`, `UNQuek`, `UNLocAvgk`, `Endpoints.QUE`.

### Findings (no target changes)
F1 (for BA-N1/BA-C2, not for this file): `UNTrLocalInit'` at window `|Re z - E| ≤ δ` reads `stieltjesN(ouInit)(z) = a⁻¹ s_{λ̂}(z/a)`, i.e. the BA local law at `λ̂` on `|Re z' - E| ≤ (δ + |E|(1-a))/a`, strictly larger than `δ`; the value shift is absorbed by the `t*` term of the tolerance (`C = 0.30 < 1`), the window growth is not. The row `UNTrLocalInitBARow'` assumes bulk stability (`κ/2`) only on `|x - E| ≤ δ`, so its proof must lower `κ/2` to `κ/4` using uniform continuity of `ρ_n` beyond `δ₀` (`UNDens'` gives it only inside the box). The data above satisfy the row (`ρ ≥ 0.1779 ≫ κ/4`); the pin is satisfiable and `baBUniv_of_rows` is unaffected; this is a proof obligation of the owner, to be listed in the BA-N1 ticket.
F2: the ticket's `UNMeanBound` route needs `λ_n > 0` only through `|λ| = λ`; `WO` gives `λ_n ≥ W^{-d/2+𝔡} > 0` eventually (checked: `W ≥ 1`).

### Verdicts
- Target 1 (`UNModelC.ba`, `UNKind.ba`, `ba_spec`): PASS (definitional; mean `λΨ` Hermitian by `PsiI_isHermitian`).
- Target 2 (consumed inputs, rows, `un_claimAll_of_rowsBA`): PASS (hypotheses of owed rows are all satisfiable at the instance; no refuted pin).
- Target 3 (input rows, `unMeanBound_ba`): PASS (`2d|λ|` sharp; `n₀ = 0` at `CV₀ = 1/2`; shift `C = 0.30`; F1 caveat for the row's proof, not its statement).
- Target 4 (`BAEnd_*`, `UNQueBA_of_BAEnd_QUEL`, `baBUniv_of_rows` through `UNCoreC''`): PASS (all hypotheses of `UNCoreC''` — `UNDens'`, `UNTrLocal`, `UNTrLocalInit'`, `∃ CV₀ (UNNormBound ∧ UNMeanBound)` — hold at the data above in the deterministic parts; stochastic parts are owed rows).
- Targets 5-8 (centred flow, `λ = 0`, bad event, instances): PASS (`lamHat`, `admissible_lamHat` checked above; `λ̂` window `(𝔠, 𝔡/2)` admissible).

Verdict: PASS.

## (b) Script output - Tue Oct  6 02:24:50 UTC 2026
Branch `t/T2241`, commit `3eeab33`, merge-base with `main` `e2ec919`; scratch files in `scratchpad/T2241/`.
```
$ lake build RBM3D.BA.UNPins      -> Build completed successfully (3748 jobs)   exit 0   (0 warnings from RBM3D/BA/UNPins.lean)
$ lake build   (full library in the worktree; the root import is the hub's merge step) -> Build completed successfully (4043 jobs)   exit 0
$ printf 'import RBM3D\nimport RBM3D.BA.UNPins\n#assert_rbm_axioms\n' > pre.lean; lake env lean pre.lean    # registry pre-check, exit 0
axiom audit: 7038 theorems, 2377 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.Univ.UNLocAvgBA: 8 [no certificate]
  RBM.Univ.UNMLOutBA: 7 [no certificate]
  RBM.Univ.UNOURowBA: 6 [no certificate]
  RBM.Univ.UNEMCTE2RowBA: 5 [no certificate]
  RBM.Univ.UNJakUywRowBA: 5 [no certificate]
  RBM.Univ.UNClaimRowBA: 4 [no certificate]
  RBM.Univ.UNDensBARow': 3 [no certificate]
  RBM.Univ.UNTrLocalBARow: 2 [no certificate]
  RBM.Univ.UNTrLocalInitBARow': 3 [no certificate]
  RBM.Univ.UNNormBARow: 3 [no certificate]
  RBM.BA.BAEnd_QUEL: 3 [no certificate]
```
`#print axioms` of the headline declarations, then `#axcheck` (script `axcheck.lean`) over all 94 public declarations of the file:
```
'RBM.Univ.un_claimAll_of_rowsBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unMeanBound_ba' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.UNQueBA_of_BAEnd_QUEL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.baBUniv_of_rows' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.BAInst.inst_univ_ba' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.BAInst.inst_step1GoodC''_ba' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.BAInst.inst_unMeanBound_ba' depends on axioms: [propext, Classical.choice, Quot.sound]
94 declarations depend on exactly [Classical.choice, Quot.sound, propext]
declarations with a non-standard axiom: 0
```
Target theorems, text extracted from the file by script `stmts.py` (`[line]`; the first five in full, the rest cut at 210 characters). The pins `UNQueBA`, `UNLocAvgBA`, `UNMLOutBA`, the four BA rows, `UNDensBARow'`, `UNTrLocalBARow`, `UNTrLocalInitBARow'`, `UNNormBARow`, `BAqueConclL`, `BAEnd_QUEL`, `BAEnd_BUnivL`, `UNKind.ba` are compared with the check file by compiled `rfl` in the next block:
```
[73] UNModelC.ba_spec : ∀ {d : ℕ} (sz : Sizes d), (UNModelC.ba sz).toUNModel = UNModel.ba sz ∧ ∀ n : ℕ, (UNModelC.ba sz).mean n = (sz.lam n : ℂ) • PsiI d (sz.L n) (sz.W n)
[142] un_claimAll_of_rowsBA (rC : UNClaimRowBA) (rE : UNEMCTE2RowBA) (rJ : UNJakUywRowBA) (rO : UNOURowBA) (hML : ∀ d : ℕ, UNMLOutBA d) (hLoc : UNLocAvgBA) (hQ : UNQueBA) : ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, (∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) κ E) → UNClaimAllC sz (UNModelC.ba sz) E
[285] unMeanBound_ba {d : ℕ} (sz : Sizes d) {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) (CV₀ : ℝ) (hCV : 0 < CV₀) : UNMeanBound sz (UNModelC.ba sz) CV₀
[357] UNQueBA_of_BAEnd_QUEL (h : ∀ d : ℕ, BAEnd_QUEL d) : UNQueBA
[367] baBUniv_of_rows (hcore : UNCoreC'') (h32 : UNL32) (hGL : UNGUELocal) (hGC : UNGreenCorrAllC) (rD : UNDensBARow') (rT0 : UNTrLocalBARow) (rT : UNTrLocalInitBARow') (rN : UNNormBARow) (rC : UNClaimRowBA) (rE : UNEMCTE2RowBA) (rJ : UNJakUywRowBA) (rO : UNOURowBA) (hML : ∀ d : ℕ, UNMLOutBA d) (hLoc : UNLocAvgBA) (hQ : UNQueBA) (d : ℕ) : BAEnd_BUnivL d
[407] ouMatC_ba_eq_ouMat (sz : Sizes d) (s : ℕ → ℝ) (n : ℕ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) : ouMatC (UNModelC.ba sz) n (s n) ω = ouMat (UNModel.ba (sz.withLam (lamHat sz s))) n (s n) ω
[438] ouP_ba_withLam (sz : Sizes d) (g : ℕ → ℝ) (n : ℕ) : ouP (UNModelC.ba sz).toUNModel n = ouP (UNModel.ba (sz.withLam g)) n
[467] ouP_ba_eq_band (sz : Sizes d) (n : ℕ) : ouP (UNModelC.ba sz).toUNModel n = ouP (UNModel.band (sz.withLam 0)) n
[445] ouMatC_ba_eq_band_add (sz : Sizes d) (n : ℕ) (t : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) : ouMatC (UNModelC.ba sz) n t ω - ((sz.lam n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) = ouMat (UNModel.band …
[472] ouInit_ba (sz : Sizes d) (s : ℕ → ℝ) (n : ℕ) (ω : Sizes.SeqΩ sz) : ouInit (UNModelC.ba sz) n (s n) ω = Real.exp (-(s n) / 2) • (UNModel.ba (sz.withLam (lamHat sz s))).H n ω
[503] admissible_lamHat {sz : Sizes d} {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) (s : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hs1 : ∀ n, s n ≤ 1) : (sz.withLam (lamHat sz s)).Admissible 𝔠 (𝔡 / 2)
[532] ba_zero_H {sz : Sizes d} (h : ∀ n, sz.lam n = 0) (n : ℕ) (ω : Sizes.SeqΩ sz) : (UNModelC.ba sz).H n ω = (UNModel.band (sz.withLam 0)).H n ω
[539] ba_zero_mean {sz : Sizes d} (h : ∀ n, sz.lam n = 0) (n : ℕ) : (UNModelC.ba sz).mean n = ((UNModel.band (sz.withLam 0)).toC).mean n
[546] ouMatC_ba_zero {sz : Sizes d} (h : ∀ n, sz.lam n = 0) (n : ℕ) (t : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) : ouMatC (UNModelC.ba sz) n t ω = ouMatC (UNModel.band (sz.withLam 0)).toC n t ω
[555] UNEMCTE2k_ba_zero {sz : Sizes d} (h : ∀ n, sz.lam n = 0) (E : ℝ) (nf : ℕ) (τU Cn : ℝ) : UNEMCTE2k (UNKind.ba d) sz E nf τU Cn ↔ UNEMCTE2k (UNKind.band d) (sz.withLam 0) E nf τU Cn
[565] UNJakk_ba_zero {sz : Sizes d} (h : ∀ n, sz.lam n = 0) (E : ℝ) (nf : ℕ) (τU C c' : ℝ) : UNJakk (UNKind.ba d) sz E nf τU C c' ↔ UNJakk (UNKind.band d) (sz.withLam 0) E nf τU C c'
[575] UNUywk_ba_zero {sz : Sizes d} (h : ∀ n, sz.lam n = 0) (E : ℝ) (nf : ℕ) (τU C c' : ℝ) : UNUywk (UNKind.ba d) sz E nf τU C c' ↔ UNUywk (UNKind.band d) (sz.withLam 0) E nf τU C c'
[594] BASelf_msc (d L : ℕ) [NeZero L] {z : ℂ} (hz : 0 < z.im) : BASelf d L 0 z (msc z)
[639] unBadY_subset' (hL : 3 ≤ L) {lamV lamQ 𝔡 E : ℝ} (hW : 1 ≤ (W : ℝ)) (h𝔡 : 0 < 𝔡) (hlam : (W : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ lamQ) (y : Idx d L W) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (h : UNBadY d L W lam…
[722] SBR_zero_ne {b a : Zd d L} (h : SBR d L 0 b a ≠ 0) : b = a
[729] unBadYBA_subset (hL : 3 ≤ L) {lamQ 𝔡 E : ℝ} (hW : 1 ≤ (W : ℝ)) (h𝔡 : 0 < 𝔡) (hlam : (W : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ lamQ) (y : Idx d L W) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (h : UNBadY d L W 0 𝔡 E y…
[738] unBadYBA_measure_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (hL : 3 ≤ L) {lamQ 𝔡 E : ℝ} (hW : 1 ≤ (W : ℝ)) (h𝔡 : 0 < 𝔡) (hlam : (W : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ lamQ) (y : Idx d L W) (Mf : Ω → Ma…
```
Check-file equality: scratch = the check file + `import RBM3D.BA.UNPins` + 38 acceptance `example`s (`KBA @UNModelC.ba d = UNKind.ba d := rfl`; `UNModelCba_spec := @UNModelC.ba_spec`; the 9 Mba-pins, `UNMLOutBA_pin`, `UNDensBARow'_pin`, `lamHat`, `BAqueConclL`, `BAEnd_QUEL`, `BAEnd_BUnivL` by `rfl`; the 21 `_stmt` theorems by `:= @Y`):
```
$ lake env lean scratchpad/T2241/acc_check.lean > acc_check.out 2>&1; echo $?; grep -c error acc_check.out
0
0
```
Verbatim against the probe (script `verb.py`, whitespace-normalised, from `def`/`theorem`; only the listed substitutions applied):
```
IDENTICAL 19 of 19: UNMLOutBA, lamHat, admissible_lamHat, unBadY_subset', SBR_zero_ne, unBadYBA_subset, unBadYBA_measure_le, fp, fp_kappa_pos, clsSz, clsSz_L_le_W, clsSz_tendsto, clsSz_bandwidth, clsSz_WO, clsSz_admissible, clsS, clsκ, clsκ_pos, cls_bulk
DIFFERS/MISSING: none   [applied: `admissible_lamHat` gets `{sz : Sizes d}` (probe `variable {sz}`); `cls_bulk` loses `huniq` and `huniq ..` becomes `baMUniqReal_holds 3 ..`; `RBM.BA.Inst` -> `RBM.BA.UNPinsInst`]
```
Refuted-pin grep (script `refuted.py`; the ticket's `grep -w` form also matches the primed successors), `seqP` grep, hygiene grep:
```
strict (primed names excluded): lines with a refuted name in the whole file: [23, 29, 30, 176]
strict, outside docstrings/comments: none
literal grep -w semantics (a trailing ' is a non-word char, so UNCoreC'' and UNTrLocalInit' match): 17 lines; outside docstrings: [185, 367, 1063]
    185 UNTrLocalInit' sz (UNModelC.ba sz) (fun n => BAm d (sz.L n) (sz.lam n)) E δ
    367 theorem baBUniv_of_rows (hcore : UNCoreC'') (h32 : UNL32) (hGL : UNGUELocal) (hGC : UNGreenCorrAllC)
    1063 theorem inst_univ_ba (hcore : UNCoreC'') (h32 : UNL32) (hGL : UNGUELocal) (hGC : UNGreenCorrAllC)
$ grep -n "seqP sz\b\|sz.seqP" RBM3D/BA/UNPins.lean                       -> no output (exit 1)
$ grep -nw "sorry\|admit\|axiom\|native_decide" RBM3D/BA/UNPins.lean       -> no output (exit 1)
```
Compiled instances of target 8 (script `inst2.py`; hypotheses listed are pins of other gates or numeric premises; every deterministic hypothesis is discharged). 8(a) `RBM.BA.UNPinsInst`: `fp`, `fp_kappa_pos`, `clsSz`, `clsSz_L_le_W`, `clsSz_tendsto`, `clsSz_bandwidth`, `clsSz_WO`, `clsSz_admissible`, `clsS`, `clsκ`, `clsκ_pos`, `cls_bulk` (no hypothesis). 8(b) `RBM.Univ.BAInst` (`S0`, `S0_adm`, `S0_bulk`, `zpt`, `zpt2` omitted):
```
inst_UNOUQUEk [898]: UNOUQUEk (UNKind.ba 3) S0 (1 / 10) τU
inst_UNOUDiagk [908]: UNOUDiagk (UNKind.ba 3) S0 τU
inst_UNEMCTE2k [924]: (hτ : 0 ≤ τU; deterministic), UNEMCTE2k (UNKind.ba 3) S0 (fp 4 UNPins_hg_3_…
inst_UNJakk [947]: (hτ : 0 ≤ τU; deterministic), UNJakk (UNKind.ba 3) S0 (fp 4 UNPins_hg_3_10)…
inst_UNUywk [962]: (hτ : 0 ≤ τU; deterministic), UNUywk (UNKind.ba 3) S0 (fp 4 UNPins_hg_3_10)…
inst_UNQueBA [980]: UNQueBA
inst_UNLocAvgBA [1001]: UNLocAvgBA
inst_UNMLOutBA [1015]: UNMLOutBA 3
inst_UNOURowBA [1027]: UNOURowBA, ∀ d : ℕ, UNMLOutBA d, UNLocAvgBA, UNQueBA
inst_UNEMCTE2RowBA [1033]: UNEMCTE2RowBA
inst_UNJakUywRowBA [1041]: UNJakUywRowBA, UNOURowBA, ∀ d : ℕ, UNMLOutBA d, UNLocAvgBA, UNQueBA
inst_claimAll_ba [1052]: UNClaimRowBA, UNEMCTE2RowBA, UNJakUywRowBA, UNOURowBA, ∀ d : ℕ, UNMLOutBA d, UNLocAvgBA, UNQueBA
inst_univ_ba [1063]: UNCoreC'', UNL32, UNGUELocal, UNGreenCorrAllC, UNDensBARow', UNTrLocalBARow, UNTrLocalInitBARow', UNNormBARow, UNClaimRowBA, UNEMCTE2RowBA, UNJakUywRowBA,
inst_step1GoodC''_ba [1120]: UNDensBARow', UNTrLocalInitBARow', UNNormBARow, UNLocAvgBA
inst_UNOUQUEk_zero [1201]: UNQueBA
inst_BAEnd_QUEL [1225]: BAEnd_QUEL 3
inst_UNQueBA_of_BAEnd_QUEL [1238]: ∀ d : ℕ, BAEnd_QUEL d
no pin hypothesis (`*`: only a numeric premise): inst_admissible_lamHat, inst_ouMatC_ba_eq_ouMat, inst_unMeanBound_ba, badYBA_zero, inst_badYBA_subset,
inst_badYBA_measure, PsiI_entry_one, inst_ba_mean_ne_zero, inst_UNModelC_ba_spec, inst_ouP_ba, inst_ouMatC_ba_eq_band_add, inst_ouInit_ba, inst_ba_zero,
inst_ba_zero_pins, inst_BASelf_msc, inst_unBadY_subset', inst_SBR_zero_ne, inst_locAvg_domain*, inst_window_sub_ba*  (19 instances)
```
Name-clash grep (script `clash.py`: `grep -rnF` of the ticket's list and of every public name of the file over `RBM3D/`, `RBM3D.lean`, except `Probe/`, `UNPins.lean`, `Test/Axioms.lean`; substring hits / whole-identifier hits; names without a hit omitted):
```
S0: substring-hits=181 whole-name-hits=24
UNDensBARow': substring-hits=1 whole-name-hits=1
UNKind.ba: substring-hits=43 whole-name-hits=0
baBUniv_of_rows: substring-hits=2 whole-name-hits=2
fp: substring-hits=7 whole-name-hits=0
inst_claimAll_ba: substring-hits=2 whole-name-hits=0
inst_step1GoodC''_ba: substring-hits=2 whole-name-hits=0
ouInit_ba: substring-hits=1 whole-name-hits=0
names checked: 106 ; total whole-name hits outside UNPins.lean and Test/Axioms.lean: 27
$ git diff --stat main...t/T2241
 RBM3D/BA/UNPins.lean   | 1312 ++++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean |   12 +
 2 files changed, 1324 insertions(+)
```

Narrative (b):
1. Source: the compiled probe `RBM3D/Probe/T2173Pins.lean` (`t/T2173` at `a543154`), the class-sequence block as copied from T2161 (`82e72b3`). No RBM1D/RBM2D text is ported (ticket: none), so there is no RBM1D/RBM2D diff-stat.
2. File: 1312 lines, 94 public declarations, 6 private helpers (`UNPins_*`); imports exactly those of the check file (`RBM3D.BA.FlowPins`, `RBM3D.Universality.PinsC2`, `RBM3D.Endpoints`, `RBM3D.Defs.Neighbours`, three Mathlib files); the diff stat lists only `UNPins.lean` and the registry file.
3. New proof `unMeanBound_ba` (file lines 196-306, 111 lines with helpers; stop rule 220): `UNPins_eig_le_rowsum` (the argument of the private `FlowPins_eig_le`, `FlowPins.lean:734`, at a general Hermitian matrix, re-proved), `UNPins_psiI_rowsum` (row sum of `Psi` is `2d`, `RBM.card_adj`), `lam_n <= 𝔡⁻¹` eventually from `WO`, `2d 𝔡⁻¹ <= N^{CV₀}` eventually from `tendsto_rpow_atTop`.
4. `UNNormBARow` gives `0 <= CV₀` only and `unMeanBound_ba` needs `0 < CV₀`: `baBUniv_of_rows` uses the norm bound at `CV₀ + 1` (`UNPins_normBound_mono`) and `unMeanBound_ba` at `CV₀ + 1`, as in the ticket's sketch; `inst_step1GoodC''_ba` does the same, so its regularity exponent is `CV₀ + 1 + 1`.
5. Differences from the probe text beyond the ticket's substitution list: (i) `admissible_lamHat` has `{sz : Sizes d}` in its signature; (ii) `inst_admissible_lamHat` is at `tau_s = 1/100` (probe `1/79200`), consistent with `inst_ouMatC_ba_eq_ouMat`; (iii) `inst_UNJakUywRowBA` takes `rO hML hLoc hQ` instead of a hypothesis `UNOUClaimsk ..` (the first registry pre-check listed `RBM.Univ.UNOUClaimsk` as a 12th unclassified premise); (iv) `inst_UNMLOutBA` uses the merged `t0_sz0 : 2/3 <= BAflowT0 ..` (probe `1/16`) and no `BAmExists 3`; (v) `unBadYBA_measure_le` has `{Ω : Type*}` as in the probe (the check file has `Type`; the compiled `example` accepts it).
6. Extra instances, so that every target theorem has one: `inst_UNModelC_ba_spec`, `inst_BAEnd_QUEL`, `inst_UNQueBA_of_BAEnd_QUEL`, `inst_ouP_ba`, `inst_ouMatC_ba_eq_band_add`, `inst_ouInit_ba`, `inst_ba_zero`, `inst_ba_zero_pins`, `inst_BASelf_msc`, `inst_unBadY_subset'`, `inst_SBR_zero_ne`; `inst_ouMatC_ba_eq_ouMat` has the extra conjunct `lamHat_n != lam_n`.
7. Not ported (ticket): `ouMat_eq_ouMatNC_add`, `ouMat_band`, `ouMatNC_sub_ouMat`, `drift_entry`, `drift_not_absorbable`, `un_shift_absorb`. Dropped instances (ticket): `inst_UNStep1GoodC` (refuted pin), `inst_shift_absorb`, `inst_drift_not_absorbable`, `inst_drift_ne_zero`, `inst_que_exponent_ba`, `inst_que_params_ba`, `inst_cprime_ba`, `inst_claim_exponent_ba`, `svarF_ne_zero_profile`, `seqGvar_ne_withLam_zero`, `unMy_single_self_zero`. Not targets: `BAGbEXPii/ij/av`, any proof of an owed row.
8. Refuted pins: the ticket's literal `grep -w` form also matches the primed successors (`'` is not a word character): lines 185, 367, 1063 (code, `UNTrLocalInit'` and `UNCoreC''`); the strict form lists docstring lines only (23, 29, 30, 176).
9. Registry: 11 `owedProps` lines (owners in the comments), pre-check exit 0. `UNQueBA`, `BAEnd_BUnivL`, `UNMeanBound` are concluded here and not registered; the pre-check did not flag `BAbulk`, `BAFlow`, `IsTestFun`.
10. Name clash: the only same-name hit is `S0` at `Graph/LWStein.lean:1907` (`RBM.Graph.LWInstOwx.S0`, a different fully qualified name). Public names for the dispatcher's check against T2240: `RBM.BA.BAqueConclL`, `RBM.BA.BAEnd_QUEL`, and the 94 names of `scratchpad/T2241/pubnames.txt`.

## (c) Verified Mathlib names (module by `env.getModuleIdxFor?`, script `mods.lean`; none checked absent)
- `Matrix.IsHermitian.mulVec_eigenvectorBasis`, `.eigenvalues`, `.eigenvectorBasis`: Mathlib.Analysis.Matrix.Spectrum
- `Finite.exists_max`: Mathlib.Data.Fintype.Lattice
- `tendsto_rpow_atTop`: Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
- `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_pos_of_pos`, `Real.rpow_le_one_of_one_le_of_nonpos`, `Real.pow_rpow_inv_natCast`: Mathlib.Analysis.SpecialFunctions.Pow.Real
- `Filter.Tendsto.eventually_ge_atTop`: Mathlib.Order.Filter.AtTopBot.Tendsto
- `Equiv.sum_comp`: Mathlib.Algebra.BigOperators.Group.Finset.Defs; `Fintype.sum_prod_type`: Mathlib.Data.Fintype.BigOperators
- `Finset.sum_boole`: Mathlib.Algebra.BigOperators.Ring.Finset; `Matrix.kroneckerMap_apply`: Mathlib.LinearAlgebra.Matrix.Kronecker
- `Real.one_lt_exp_iff`: Mathlib.Analysis.Complex.Exponential; `Real.exp_one_lt_d9`: Mathlib.Analysis.Complex.ExponentialBounds
- `MeasureTheory.measure_mono`: Mathlib.MeasureTheory.OuterMeasure.Basic
- `Matrix.inv_eq_right_inv`, `Matrix.nonsing_inv_eq_ringInverse`: Mathlib.LinearAlgebra.Matrix.NonsingularInverse; `eq_inv_of_mul_eq_one_left`: Mathlib.Algebra.Group.DivInvMonoid

## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none. The law of the BA chain is T2173a, `rho_N >= kappa` is DECISIONS §51, the dilated form is §11 (cited, not re-proposed).
- (a′): no correction to (a). Finding F1 of (a) is unchanged: it is a proof obligation of the owners of `UNTrLocalInitBARow'` (BA-N1) and `UNDensBARow'` (BA-C2); the rows are stated as the ticket pins them.
- Hypotheses left in the instances: the 11 registered pins; the T2187 claim pins `UNOUQUEk`, `UNOUDiagk`, `UNEMCTE2k`, `UNJakk`, `UNUywk` at `S0`; `UNCoreC''`, `UNL32`, `UNGUELocal`, `UNGreenCorrAllC`. `S0` uses the Classical-chosen flow point `fp 4 _` (`g0 <= 3/10`, not computable here).
- The ticket's literal refuted-pin grep cannot have zero code hits, because `UNCoreC''` and `UNTrLocalInit'` contain the unprimed words (narrative 8).
