Prover model: claude-sonnet-5-5
## (a) Math preflight — Mon Oct 12 17:47:53 UTC 2026
Tree `main` e288560e (worktree `t/T2463`); no Lean written. Targets 1-10 as in `docs/tickets/T2463.md`, pins `T2463_*` in `docs/tickets/checks/T2463-check.lean:154-330`.

### (i) Exponent table
No analytic exponent, `≺`, `ε`, `𝔡`, `𝔠` or `PrecL` occurs in `T2463_*` (check:154-330); the only exponents are the loop-length exponents `m - k_α` and the algebraic constants below. `sz.lam`/`g`/`gK`/`A` are not read by targets 1-6 (grep over check:154-330: 0 hits; first hits are the non-binding band-route and BA examples, check:342-362). So the UBA-C1 comparison `∀ n, 0 ≤ gK n ∧ gK n ≤ sz.lam n ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2` is not used by any target.

| quantity | value at the instance | constraint (source) | slack |
|---|---|---|---|
| `d` | 3 | any `d : ℕ`; no `3 ≤ d` in `T2463_*` | n/a |
| `L` (`sz0.L 0`) | 4 | only band target 1 needs `3 ≤ L` (`sum_SB_row`, `Defs/Block.lean:108`; `sz.three_le_L`); targets 2-6 read target 1 instead | 1 |
| `W` (`sz0.W 0`) | 32 | `W ≥ 1` (`Sizes.W_pos`, `Defs/Sizes.lean:146`): `NeZero W`, κ defined | 31 |
| `N = (WL)^d` | 2097152 = 2^21 | `Sizes.size`; `(L^d)⁻¹ (2i W^d η)⁻¹ = (2i N η)⁻¹` (target 4 → 5 coefficient) | equality (script B) |
| `E` | 0, `Im mE = 1` | band class `|E n| < 2` (`mE_im_pos`, `Defs/Semicircle.lean:56`); `Step2Gen_USemigroup` band: `|E n| ≤ 2` | 2 |
| `τ`, `η = (1-τ) Im m` | 1/2, 1/2 | `0 ≤ τ < 1` (class `T2463_WardCls`); `η ≠ 0` only for `κ` to be the Ward constant | 1/2 |
| `κ = (2i W^d η)⁻¹` | `-i/32768` at `W = 32`; `-i/8` at `W = 2` (script B) | Ward constant of `WardFam` (both `loopL` and `KLK_ward`, `Loop/KLWard.lean:1318`) | n/a |
| `L^{-d} κ` | `-i/2^21` | coefficient base of `zeroModeGen_newPQ` | n/a |
| `m`, `k_α` | `m = 3`, `k_α ∈ {1,2}` | `1 ≤ k_α`, `k_α + 1 ≤ m` (so `m - k_α ≥ 1`) | `m - k_α ∈ {2,1}` |
| `|coef|` | `2^-21` (`m-k=1`), `2^-42` (`m-k=2`) | `|L^{-d}κ|^{m-k_α}` | n/a |
| `I_diff(σ)`, `σ = (+,-,+)` | `{0,1}` (script A) | `A' α ⊇ I_diff(σ' α)` | `A = ∅`, nonempty `I_diff` |
| grid | `s = 1/10, t = 1/2, K = 4, j = 4, τ(ω) = 3`; `gridTime = 0.1..0.5` | `0 ≤ s ≤ t < 1`, `K ≠ 0`, `min j τ ≤ K` (`stoppedDuhamelNg_at`, `GridDuhamelGen:261`) | `t` is `1/2` below 1; `min = 3 ≤ 4` (1) |
| semigroup window | `v = 1/10, w = 1/2, u = 2.3` | `v, w ∈ [0,1)`, `u` arbitrary (`Step2Gen_USemigroup`); needs `1 - vX` a unit | singular values of `1 - tX` ≥ `1 - t`: 0.5 at `t = 1/2`, 0.01 at `t = 0.99` (script A) |
| kernel constant `c` | `μ = m(σ)m(σ') ∈ {-1, +1}` | target 1: rows and columns of `X = M^{(σσ')} S` sum to one `c`; band `X = μ S`, `S` doubly stochastic (`Step2Kern_Mss_band`, `sum_SB_row` `Defs/Block.lean:108`, `sum_SB_col` `Kernel/Evolution.lean:353`) | n/a |
| `1 - t c` | `{3/2, 1/2}` at `t = 1/2` | `≠ 0` (target 6; forced by `IsUnit (1 - t•X)`, since `1ᵀ(1 - tX) = (1 - tc) 1ᵀ`) | 1/2 |
| column sums | `thetaKer`: `c/(1-tc) ∈ {-2/3, 2}`; `uKer` (`s = 1/10`): `(1-sc)/(1-tc) ∈ {11/15, 9/5}` | target 6 values | n/a |

**Premise table (math).**
| premise | where used | band discharge (instance) | BA |
|---|---|---|---|
| `KerSums C n` (a) | targets 2, 3, 6 | `X = μ S`, `c = μ`, `L = 4 ≥ 3` (script A) | U1-BA (`BAMB_shift`, `BAK_row_sum/col_sum`, supervisor 1457 `:110-113`) |
| `Step2Gen_USemigroup` (b) | target 3 | `|E 0| = 0 ≤ 2`, `uKer(v,v) = 1`, `uKer(v,w) uKer(u,v) = uKer(u,w)` (script A) | `BAuKer_self/comp` |
| `WardFam` / `WardCls` (c) | targets 4 (hyp), 5 | rotation + Ward for random Hermitian `H`, `z = i/2` (script B); `KLK_rotate/KLK_ward` for 𝒦 | U1-BA (`baK_ward`, `BAKsol_rotate`) |
| `IsUnit (1 - t•X)` (d) | target 6 values | `min sv = 1/2` (script A) | BA reader |
| sum-zero `STPsum A = 0` (e) | target 6 sum-zero | hypothesis as in the band | same |

**Arguments the table rests on (checked by script where numeric).**
- Target 2: constant row sums `c` and column sums `c` give `projMat X = X projMat` (`ZeroModeCalc_projMat_comm_of_sums`, ZMC:297). `Step2Gen_Theta X t = Ring.inverse (1 - tX)`: unit ⇒ the inverse commutes (`Commute.units_inv_right`), non-unit ⇒ `0` commutes. So `uKer`, `thetaKer` commute with `projMat` for every `s, t` (no `‖tμ‖ < 1`). Corner `X = 2S`, `t = 1/2`: `1 - tX = 1 - S` singular, Θ = 0, `thetaKer` column sums 0 (script A, last lines).
- Column sums constant in `y` for every `t`: unit case `1ᵀ Θ = (1 - tc)⁻¹ 1ᵀ`; non-unit case `0`. This gives the slot-`i ≥ 1` step of the sum-zero targets with no window.
- Target 3: `stoppedDuhamelNg_at` gives `A = U(A_0) + Σ U(pred + mart)`; apply `zeroModeSet` (additive, `zeroModeSet_add/sum`), `Step2Gen_UN_add`, then target 2 with `(s,t) = (gridTime 0, gridTime (min j τ))`.
- Target 5 from target 4: `ξ (L^{-d} κ)^{m-k} = ξ / (2i N η)^{m-k}` as `(L^d)⁻¹ (2i W^d η)⁻¹ = (2i (WL)^d η)⁻¹` and `sz.size n = (W n * L n)^d` (script B; same step as `stNewPQ_holds`, NewPQ.lean:599-608). Target 9 needs the separate 𝓛 and 𝒦 expansions: it follows from target 4 at the class witnesses `TL`, `TK`, not from the combined `𝓛 - 𝒦` of target 5.

### (ii) One concrete nondegenerate instance
`d = 3`, `sz0` at `n = 0` (`L = 4`, `W = 32`, `g = 1/64`, `N = 2^21`, `Defs/Sizes.lean:260-267`), `E = 0`, `σ = (+,-,+)`, `A = {0,1}` and `∅`, `τ = 1/2`, grid as in the table. Script A uses the full 64 × 64 block kernel and 64^3 tensors; script B uses `W = 2` (512 × 512, the Ward identity is for every `W ≥ 1`), a random Hermitian `H`, `z = zt(0, 1/2) = i/2`.
Script A (`S = SB`: `a₀ = (1+2dg²)⁻¹` at 0, `g² a₀` at ℓ¹-distance 1, `Defs/Block.lean:38-41`; `mE 0 = i`):
```
$ python3 inst.py
S row sums in 0.9999999999999999 0.9999999999999999  col sums 0.9999999999999999 1.0
c = mu per charge pair: {(True, True): np.complex128(-1+0j), (True, False): np.complex128(1+0j), (False, True): np.complex128(1+0j), (False, False): np.complex128(-1+0j)}
target 1 (KerSums) holds at all 4 charge pairs
gridTime j=0..4: [0.1 0.2 0.3 0.4 0.5]  all in [0,1): True
spec(S) in [0.997075, 1.000000]
t=0.50: min singular value of 1-tX (mu=+-1): 0.5000000000000001
t=0.99: min singular value of 1-tX (mu=+-1): 0.010000000000000071
target 3 premise Step2Gen_USemigroup: uKer(v,v)=1, uKer(v,w)uKer(u,v)=uKer(u,w) checked, all 4 charge pairs
   pair (True, True) c=-1: 1-tc=1.50, thetaKer colsum=-0.6667, uKer colsum=0.7333
   pair (True, False) c=+1: 1-tc=0.50, thetaKer colsum=2.0000, uKer colsum=1.8000
   pair (False, True) c=+1: 1-tc=0.50, thetaKer colsum=2.0000, uKer colsum=1.8000
   pair (False, False) c=-1: 1-tc=1.50, thetaKer colsum=-0.6667, uKer colsum=0.7333
target 6 values: col sums of thetaKer = c/(1-tc), uKer = (1-sc)/(1-tc), 1-tc in [np.float64(0.5), np.float64(1.5)]
target 2 (n=64 labels/index, tensor 64^3): max|Q^A U - U Q^A| = 2.32e-14, max|Q^A Th - Th Q^A| = 2.89e-14, scale 1.27e+01, Q^A T nonzero: 5.05e+00
corner: det(1-0.5*2S) = 9.63e-198 -> Theta=0, thetaKer col sums = 0.0
I_diff(+,-,+) = [0, 1]
```
Script B (`loopL = tr ∏ Gres(s_p) Eblk(a_p)`, `Eblk a = diag(1[x.1 = a] W^{-d})`, `Loop/GLoop.lean:55`, `Loop/GLoopFlow.lean:74,123`):
```
$ python3 ward.py
z = 0.5j  Im z = eta = 0.5
kappa = (2i W^d Im z)^-1 = -0.125j
WardFam: max rel err Ward = 2.74e-14 (both s, |mu|=1,2), max abs err rotation = 5.46e-23, |lhs| ~ 1.10e-07
P^(0) T_sigma: |lhs-rhs| = 2.41e-21 (|lhs| = 4.17e-07)
P^(1) T_sigma: |lhs-rhs| = 1.93e-21 (|lhs| = 2.15e-07)
L^-d kappa = -4.76837158203125e-07j  (2iN eta)^-1 = -4.76837158203125e-07j  N = 2097152
m=3 k=1: m-k=2, |(L^-d kappa)^(m-k)| = 2.274e-13
m=3 k=2: m-k=1, |(L^-d kappa)^(m-k)| = 4.768e-07
```
Every hypothesis holds at once: `L = 4 ≥ 3`, `W = 32 ≥ 1`, `|E| = 0 < 2`, `τ = 1/2 ∈ [0,1)`, `0 ≤ 1/10 ≤ 1/2 < 1`, `K = 4 ≠ 0`, `min j τ = 3 ≤ 4`, `KerSums` at all 4 charge pairs, `Step2Gen_USemigroup`, `IsUnit (1 - t•X)`, Hermitian `H` with `Im z = 1/2 ≠ 0`; `Q^A T ≠ 0` (size 5.05) and `Q^A U − U Q^A ≈ 2e-14`. No `N = 0`, empty index set, collapsed window or large witness. External-input limit check (TEAM §8 lesson 14): the external premises are (a)-(e); each is evaluated above at the band data, and `L^{-d}κ = (2iNη)⁻¹ = -i/2^21` is the exact value at `N = 2097152`; the BA discharge of (a), (b), (c) is U1-BA's and is not a target here.

### Verdict per target
| target | verdict | reason |
|---|---|---|
| 1 `KerSums`, `KerSumsBand` | PASS | holds at the instance for all 4 charge pairs; band reason `Step2Kern_Mss_band` + `sum_SB_row/col` |
| 2 `ZeroModeSetUNg`, `ThetaNg` | PASS | argument above, script A (2e-14 on 64^3 tensors) |
| 3 `DuhamelInsideAtg` | PASS | `stoppedDuhamelNg_at` + target 2 + additivity; all hypotheses at the grid instance |
| 4 `WardFam`, `LoopLWardFam`, `NewPQExpansion` | PASS | script B (Ward, rotation, `P^{(i)}` step at `m = 3`); same proof as private `npq_main` (`NewPQ.lean:479`), data independent of `L` and `κ` |
| 5 `WardCls`, `WardClsBand`, `LKExpansiongL`, `…EmptygL` | PASS | `TL = loopL …`, `TK = KLK` (`KLK_rotate`, `KLK_ward`); coefficient identity above |
| 6 column sums, sum-zero, `Sub`, commutators | PASS | values at the instance; sum-zero needs only target 1 |
| 7 band corollaries and instances | PASS | all data of 7 (b) are the instance above (`sz0`, `n = 0`, `τ = 1/2`) |
| 8 greps | PASS (no exponent conflict) | no target 1-6 statement except the band forms reads `g`, `lam`, `gK`; `|E n| < 2` occurs only in `T2463_WardClsBand` (check:238) |
| 9 `STNewPQgL` | conditional | `docs/queue/T2457.state`: `state: held`, updated Mon Oct 12 17:13:39 UTC 2026, so target 9 moves to U1-BA unless T2457 merges before 1b |
| 10 G1 | n/a (no math) | — |

## (b) Script output — Mon Oct 12 18:04 UTC 2026 (prover, `claude-sonnet-5-5`; branch `t/T2463`, commits 835a610f, 81ca99ae)
### Layout, cone, size against the stop line
One new file `RBM3D/Chain/ZeroModeGen.lean`, namespace `RBM.BA`, imports `GridDuhamelGen`, `ZeroModeCalc`, `QopAlgebra` only; the reserve `ZeroModeGenB` is not used; `RBM3D.lean` and the four band files are not edited.
```
$ git log --oneline -3; wc -l RBM3D/Chain/ZeroModeGen.lean
81ca99ae T2463: ZeroModeGen band corollaries and compiled instances (target 7)
835a610f T2463: ZeroModeGen targets 1-6 (kernel premise, commutation, Duhamel inside, newPQ, Ward class, QopAlgebra readings)
e288560e T2459: merge U U5 design report (report-only; probe and scripts stay on t/T2459)
     878 RBM3D/Chain/ZeroModeGen.lean
$ lake build RBM3D.Chain.ZeroModeGen 2>&1 | tail -3

Note: This linter can be disabled with `set_option linter.style.header false`
Build completed successfully (3766 jobs).
$ # axioms of the 28 public declarations (#print axioms, scratch ax.lean)
  28 [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Chain/ZeroModeGen.lean | wc -l
       0
$ lake env lean pins.lean  (check file Parts 1-2 + `example : T2463_X := @name` for the 20 pins); error lines:
0
$ lake env lean docs/tickets/checks/T2463-check.lean; echo $?
0
$ lake env lean pre.lean  (import RBM3D; import RBM3D.Chain.ZeroModeGen; #assert_rbm_axioms)
axiom audit: 13482 theorems, 4280 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
exit 0
$ grep -rl "import RBM3D.Chain.ZeroModeGen" RBM3D RBM3D.lean | wc -l      # reverse cone of the new file
       0
$ git diff main...t/T2463 --stat ; git diff main...t/T2463 --stat -- RBM3D/Induction RBM3D/Chain/Carrier.lean RBM3D/Chain/Step2Gen.lean RBM3D/Chain/Step2Kern.lean RBM3D/Chain/GridDuhamelGen.lean RBM3D/Chain/Step5Gen.lean RBM3D/BA | wc -l
 RBM3D/Chain/ZeroModeGen.lean | 878 +++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 878 insertions(+)
       0
```
878 lines against the stop line 2,000 (estimate 650 / 950 / 1,500). G1: the diff of the four band files and the other listed files is empty; Part 3 names unchanged (their files are untouched, and the check file compiles on the branch, exit 0 above).
### T2457 status and target 9
```
$ head -1 docs/queue/T2457.state; git ls-tree main --name-only RBM3D/Chain/ | grep Step34Gen; echo rc=$?
state: held
rc=1
```
T2457 is `held` and `Chain/Step34Gen.lean` is not on `main` (e288560e): target 9 (`stNewPQgL_wardCls`) is **not written**; it moves to U1-BA, count-neutral (ticket target 9, T2458 target 11 precedent). No import of `Step34Gen`.
### Statements against the `T2463_*` pins
Pins: `docs/tickets/checks/T2463-check.lean:154-328`. Every `Prop`-valued pin is closed by the theorem of the same content (`example : T2463_X := @name`, 20 lines, scratch `pins.lean` = check file lines 1-336 + the `import RBM3D.Chain.ZeroModeGen` + the 20 examples; 0 error lines above). The three defined `Prop`s are `Iff.rfl` with the pins (`KerSums`, `WardFam`, `WardCls`). Name map: `T2463_KerSumsBand` = `zeroModeGen_kerSums_band`; `ZeroModeSetUNg`/`ThetaNg` = `zeroModeSet_UNg`/`zeroModeSet_ThetaNg`; `DuhamelInsideAtg` = `zeroModeCalc_duhamel_inside_atg`; `LoopLWardFam` = `zeroModeGen_loopL_wardFam`; `NewPQExpansion` = `zeroModeGen_newPQ`; `WardClsBand` = `zeroModeGen_wardCls_band`; `LKExpansiongL`/`EmptygL` = `zeroModeCalc_LK_expansiong`/`_emptyg`; `ColSumThetaKerg`/`UKerg`, `ThetaNSumZerog`/`UNSumZerog`, `ThetaNSubg`/`UNSubg`, `CommutatorThetaNg`/`UNg` = `QopAlgebra_*g`. Public declarations (28), from the file:
```
$ grep -nE "^(theorem|def) " RBM3D/Chain/ZeroModeGen.lean | sed -E 's/^([0-9]+):(theorem|def) ([A-Za-z0-9_]+).*/\1 \3/' | tr '\n' ' '
54 ZeroModeGen_KerSums 60 zeroModeGen_X_band 66 zeroModeGen_rowSum_band 75 zeroModeGen_colSum_band 85 zeroModeGen_kerSums_band 92 zeroModeGen_isUnit_band 115 zeroModeGen_projMat_comm_X 122 zeroModeGen_projMat_comm_uKer 134 zeroModeGen_projMat_comm_thetaKer 161 zeroModeSet_UNg 170 zeroModeOp_ThetaNg 179 zeroModeSet_ThetaNg 197 zeroModeCalc_duhamel_inside_atg 226 ZeroModeGen_WardFam 234 zeroModeGen_loopL_wardFam 249 zeroModeGen_newPQ 289 ZeroModeGen_WardCls 299 zeroModeGen_wardCls_band 329 zeroModeCalc_LK_expansiong 364 zeroModeCalc_LK_expansion_emptyg 419 QopAlgebra_col_sum_thetaKerg 427 QopAlgebra_col_sum_uKerg 462 QopAlgebra_ThetaN_sumZerog 485 QopAlgebra_UN_sumZerog 522 QopAlgebra_ThetaN_subg 529 QopAlgebra_UN_subg 536 QopAlgebra_commutator_ThetaNg 550 QopAlgebra_commutator_UNg
```
### Compiled nonempty instances (`d = 3`, `sz0`, `n = 0`, `bandFM sz0 (fun _ => 0)`, `σ = (+,-,+)`, `τ = 1/2`; section 8, namespace `ZeroModeGenInst`)
```
$ grep -n "^/-- Target [0-9]" RBM3D/Chain/ZeroModeGen.lean | cut -c1-118
```
689:/-- Target 1 at `bandFM sz0`, `n = 0`. -/
692:/-- Target 2 (`Step2Gen_UN`): `Q^{(A)}`, `A = I_diff(σ)` (two indices), commutes with `U_{9/10, 99/100}` on the
702:/-- Target 2 (`Step2Gen_ThetaN`), same data. -/
711:/-- Target 3 at `bandStep2Mat sz0`: `s ≡ 1/10`, `t ≡ 1/2`, `K ≡ 4`, `τ ≡ 3`, `j = 4` (`j ∧ τ = 3 ≤ K = 4`),
735:/-- Target 4 (`zeroModeGen_loopL_wardFam`) at the Hermitian matrix `H_{1/2}(ω)` of the model on the block-product
744:/-- Target 4 (`zeroModeGen_newPQ`): `d = 3`, `m = 3`, `σ = (+,-,+)`, `A = ∅`, applied to the G-loops of the model 
768:/-- Target 5, the class at `bandFM sz0` (`|E n| < 2`). -/
772:/-- Target 5, `zeroModeCalc_LK_expansion_emptyg` (`A = ∅`) at `bandFM sz0`, `n = 0`, `τ = 1/2`, `m = 3`,
791:/-- Target 5, `zeroModeCalc_LK_expansiong` for the nonempty `A = {2}` (`A ∪ I_diff(σ) = {0, 1, 2}`), same data. -/
810:/-- Target 6, column sums of `Step2Gen_thetaKer` and `Step2Gen_uKer` at `bandFM sz0`, `n = 0`, charges
836:/-- Target 6, `Θ^{(3)}` and `U^{(3)}` preserve the sum-zero tensor `𝒬_{1/2} 1` at `bandFM sz0`. -/
845:/-- Target 6, linearity and the commutators at the same data (the tensor `δ₀`, the label `a = 0`). -/
```
Section 7 (a) band examples at lines 573-651 (`Ind.zeroModeSet_Ugen`, `Ind.zeroModeCalc_duhamel_inside_at` at `bandStep2Mat`, `zeroModeCalc_LK_expansion` and `_empty`, `QopAlgebra_ThetaN_sumZero`, `QopAlgebra_col_sum_thetaKer`), derived from the generic targets through `bandStep2_*`, `Step2Kern_*_band`, `zeroModeGen_*_band`; they need none of `3 ≤ L`, `‖μ_i‖ = 1`, `0 ≤ w < 1`. Every deterministic hypothesis of the section 8 instances is discharged at the data (`step2Gen_USemigroup_band`, `zeroModeGen_kerSums_band`, `zeroModeGen_wardCls_band`, `zeroModeGen_isUnit_band`, `Sizes.gLoopFlow_seqHflow_isHermitian`, `etaT_pos`); `δ₀ ≠ 0` and `|I_diff(σ)| = 2` are proved in the first two instances; the sum-zero tensor is `𝒬_{1/2} 1` of the merged mollifier (`QopAlgebra_Psum_Qop`). No premise is another gate's pin.
### Scope, hypothesis and bridge tables as finally used (1a (iii)-(v)); `open private` list (1a (vi))
Scope (58 public names, counts from check Part 3: ZMC 36, NPQ 1, QA 19, QopNorm 2):
| group (names) | n | disposition | readers |
|---|---|---|---|
| ZMC `zeroModeOp_add/_smul/_sum/Lin`, `zeroModeSet_add/_smul/Lin/_zero/_sub/_sum/_empty`, `norm_zeroModeOp_le`, `norm_zeroModeSet_le` | 13 | model-free, reused | targets 3, 5 (here) |
| ZMC `tensorKer_zeroModeOp`, `zeroModeOp_tensorKer_comm`, `zeroModeSet_comm_of_comm`, `zeroModeSet_tensorKer_comm`, `projMat_comm_of_sums` | 5 | model-free, reused | targets 1, 2 |
| ZMC `mem_STIdiff`, `STIdiff_subset_iff`, `sameSignOutside_*` | 4 | model-free, reused | T2457 / U3 |
| ZMC `projMat_mul_Theta_comm`, `_uKer_comm`, `_thetaKer_comm` | 3 | band only (replaced by `zeroModeGen_projMat_comm_uKer/_thetaKer`) | target 2 |
| ZMC `zeroModeSet_UN`, `zeroModeSet_ThetaN`, `zeroModeOp_ThetaN` | 3 | generic: `zeroModeSet_UNg`, `zeroModeSet_ThetaNg`, `zeroModeOp_ThetaNg` | U3s4, V1, U1-BA |
| ZMC `zeroModeOp_UN`, `Ind.zeroModeOp_Ugen` | 2 | band only (no outside reader; optional) | — |
| ZMC `Ind.Ugen_eq_UN_EKsgn`, `Ind.zeroModeSet_Ugen` | 2 | band only (`Ugen = Step2Gen_UN` is T4s1's `bandStep2_Ugen`; §7 example) | T2457 |
| ZMC `Ind.zeroModeCalc_duhamel_at` / `_inside_at` | 2 | private step / generic `zeroModeCalc_duhamel_inside_atg` | U3s4 |
| ZMC `LK_expansion`, `_empty`; NPQ `stNewPQ_holds` | 3 | generic `zeroModeCalc_LK_expansiong`, `_emptyg`; `zeroModeGen_newPQ` | U3s4, U1-BA |
| QA mollifier family (11: `mollifier*`, `stMollifierEx_holds`, `Psum_*`, `Qop_*`) | 11 | model-free, reused | U3s3, U1s2 |
| QA `col_sum_thetaKer/uKer`, `ThetaN/UN_sumZero`, `ThetaN/UN_sub`, `commutator_ThetaN/UN` | 8 | generic `QopAlgebra_*g` | U2, U3s3, U1s2, V1s3 |
| QopNorm `stQopNorm_holds`, `stQop_sub_fastDecay` | 2 | model-free, reused | — |
Hypotheses (band fact -> generic premise -> band discharge -> BA source): `3 ≤ L`, symmetric `Theta`, `‖tμ‖ < 1` (ZMC:305-330, QA:670-711) -> `ZeroModeGen_KerSums` -> `zeroModeGen_kerSums_band` -> U1-BA (`BAMB_shift`, `BAK_row_sum/col_sum`, `BATheta_row_sum_pm`); `3 ≤ L`, `|E n| < 2` of the Duhamel (ZMC:522) -> `Step2Gen_USemigroup` + `KerSums` -> `step2Gen_USemigroup_band` -> `BAuKer_self/comp`; `|E n| < 2` (ZMC:563) -> `ZeroModeGen_WardCls` -> `zeroModeGen_wardCls_band` -> `baK_ward`, `BAKsol_rotate`, `EMn2BA_seqHflowBA_herm`; `‖tμ‖ < 1` in the explicit column sums (QA:697, 704) -> `IsUnit (1 - t X)` -> `zeroModeGen_isUnit_band` -> the BA reader; `‖μ_i‖ = 1`, `0 ≤ t < 1` of the sum-zero statements (QA:786, 821) -> none beyond `KerSums`.
Bridges: targets 2 are proved from `ZeroModeCalc_zeroModeSet_tensorKer_comm` (`Step2Gen_UN` is the tensor kernel by definition; `Step2Gen_ThetaN` is the `zmcSlot` sum by `funext`/`simp`) and `Ring.inverse` commutation (`ZeroModeGen_commute_ringInverse`); target 3 from `stoppedDuhamelNg_at`, `zeroModeSet_UNg`, additivity; target 4 `zeroModeGen_newPQ` from `npq_main` + `npq_ward_of_fam` (the list of terms becomes a `Fin ℓ` sum by `ZeroModeGen_sum_get`); target 5 from target 4 at the witnesses of the class and `L^{-d} (2 i W^d η)⁻¹ = (2 i N η)⁻¹` (`ZeroModeGen_coef`); the band class by `loopM_eq_loopL`, `KLK_rotate`, `KLK_ward`; target 6 column sums by `Ring.mul_inverse_cancel` (`ZeroModeGen_colSum_Theta`), sum-zero by `qa_slot_zero/_succ`, `qa_sum_filter_prod`, `qa_sum_fiber0` with a non-unit `1 - t X` giving `Θ = 0` (constant column sum 0).
`open private` (all reused, none copied): NPQ `npq_main`, `NPQTerm` (+ fields `k ξ σ ι A`, `val`), `NPQFam` (+ `mk`), `npq_ward_of_fam`, `npq_loopL_rotate`, `npq_loopL_ward`; ZMC `zmcSlot`, `zmcSlot_comm`; QA `qa_slot_zero`, `qa_slot_succ`, `qa_sum_filter_prod`, `qa_sum_fiber0`. Copied under the stem: `ZeroModeGen_ThetaN_eq` (= `zmc_ThetaN_eq` at the carrier kernel), `ZeroModeGen_sum_get` (= `npq_sum_get`). Not needed: `zmc_gridTime_*` (no window), `NPQTerm.lift`.
### Greps of target 8 (counts: the whole file, hits labelled)
```
$ (a) grep -cE "RBM\.UN|\bUN d|ThetaN d|uKer d|thetaKer d|Ugen|EKsgn|PropSpin|Theta d|SB d|cycProd|mSigma" F   -> 22 lines
$ (b) grep -cE "mE|zt E|zt \(|2 - κ|\|E|etaT|cltCk|norm_mE|seqHflow|Lloop|STKloop|KLK|STFlow|lemT|‖m‖" F      -> 43 lines
$ (c) grep -cE "sz\.lam|lam0|BAflowLam0|withLam|gK|ellT|Bctl" F                                              -> 27 lines
$ grep -c "Step2Gen_UN" F -> 36 ;  grep -cE "^(def|theorem|abbrev) .*Ugen" F -> 0
$ grep -n "^import" F -> 6:import RBM3D.Chain.GridDuhamelGen  7:import RBM3D.Induction.ZeroModeCalc  8:import RBM3D.Induction.QopAlgebra
```
(a) hits: lines 15 (docstring), 62-97 (band bridges `zeroModeGen_X_band`, `_rowSum_band`, `_colSum_band`, `_kerSums_band`, `_isUnit_band`), 571-652 (section 7 band examples), 814-817 (band instance); no `def` builds a kernel: the only `def`s are the `Prop`s `ZeroModeGen_KerSums` (54), `ZeroModeGen_WardFam` (226), `ZeroModeGen_WardCls` (289) and private instance data (`zmg*`, 673-681, 826-830). (b) hits: docstrings (91, 196, 224, 297-298, 328, 572, 602, 648, 663), the band theorems `zeroModeGen_isUnit_band` (91-93) and `zeroModeGen_wardCls_band` (297-315), the section 7 band examples (582-649) and the instances (740-768); no generic statement (targets 1-6) carries `|E|`, `mE`, `zt`, `etaT`, `seqHflow`, `Lloop`, `STKloop`, `KLK` (spectral data enter only as `C.eta`). (c) hits: the same band lines plus `zmgK` (a grid name; `gK` is a substring), none in a generic statement; no generic statement reads `g`, `g₀` or `lam`, so UBA-C1 is not used and no comparison hypothesis was added. (d) no `BA/*`, `CltGen`, U1s2/U2/U3/U4/V import.
### Name-clash grep (28 new public names, `git grep -nE` over `RBM3D/*.lean` at each ref, excluding the new file)
```
main e288560e: 0 hits   t/T2454 6affbeb5: 0 hits   t/T2455 8eb4ff2a: 0 hits   t/T2457 ee3d8a05: 0 hits   t/T2462 0a1203eb: 0 hits
```
Narrative (build and statements are the evidence above): the proofs reuse the band privates through `open private` (precedent `GridDuhamelGen:32`); the one new argument is that `Step2Gen_Theta` is `Ring.inverse`, so `Proj_{e^⊥}` commutes with `uKer`, `thetaKer` for every `s, t` from constant row and column sums alone, and a non-unit `1 - tX` gives `Θ = 0` with column sums 0; the explicit values need `IsUnit`. No band file, `RBM3D.lean` or `Test/Axioms.lean` was edited. Stop rules: none triggered.
## (c) Verified Mathlib names (all compile in `ZeroModeGen.lean`)
`Ring.inverse_unit`, `Ring.inverse_non_unit`, `Ring.mul_inverse_cancel`, `Commute.units_inv_right`, `Commute.zero_right`, `Commute.one_right`, `Commute.sub_right`, `Commute.smul_right`, `Commute.mul_right`, `eq_inv_of_mul_eq_one_right`, `mul_inv`, `Finset.sum_comm`, `Finset.mul_prod_erase`, `List.sum_ofFn`, `List.map_ofFn`, `List.ofFn_get`. Verified absent (not used): a Mathlib lemma `Commute a (Ring.inverse y)` from `Commute a y` (`Commute.ringInverse_ringInverse` has the form `Commute (inverse a) (inverse b)`); proved as private `ZeroModeGen_commute_ringInverse`.
## (d) Open issues and paper-delta candidates
- Target 9 (`stNewPQgL_wardCls`) not written (T2457 held, `Step34Gen` not on `main`): U1-BA, count-neutral.
- `zeroModeOp_UN` and `Ind.zeroModeOp_Ugen` (single-index forms, no outside reader) are not restated; `zeroModeOp_ThetaNg` is public because the route needs it.
- Public helpers beyond the pins (all under the stem): `zeroModeGen_X_band`, `_rowSum_band`, `_colSum_band`, `_isUnit_band`, `zeroModeGen_projMat_comm_X`, `_uKer`, `_thetaKer`, `zeroModeOp_ThetaNg`.
- T2463a: Lean's `Step2Gen_Theta` is `Ring.inverse`; the commutation and the constant column sums hold for every `s, t`, also at singular `1 - tX` (`Θ = 0`), while the paper states them for `‖tμ‖ < 1`; the explicit values keep `IsUnit`. The Lean statements are stronger than the paper's; no conflict.
- T2463b: the paper's `lem: newPQ` is stated for `𝓛`, `𝒦` of the model; Lean carries it model-free over a `ZeroModeGen_WardFam` with coefficient `(L^{-d} κ)^{m-k}`, and the model enters only through `ZeroModeGen_WardCls`.
