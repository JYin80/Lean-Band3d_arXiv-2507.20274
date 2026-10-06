Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 07:33:26 UTC 2026

### (i) Exponent table

Data of the targets (check file `docs/tickets/checks/T2268-check.lean` §3): `d ≥ 2`, `sz : Sizes d`, `n`, `E, u, κ`, `m`, `Γ ν X ωf Fv Λ τN Y`, `N = size n = (W L)^d`, `B = Bctl n u = (W^d)⁻¹ Bparam d L lam u 0`, `ℓ = ellT L lam u`, `η = etaT E u = (1-u) Im mE E`.

| quantity | value in the instance (d=3, sz0, n=0) | constraint (source) | slack |
|---|---|---|---|
| `κ, E` | `κ = 1`, `E = 0` | `0 < κ`, `|E| ≤ 2-κ` (targets 2, 3) | `1 ≤ 1`: `|E| = 0 ≤ 1` |
| `u` | `0` | `0 ≤ u < 1` | `1-u = 1` |
| `lam n` | `1/64` | `0 < lam n` | positive |
| case (i) | `N⁻¹ = 4.8e-7` | `N⁻¹ ≤ 1-u` (B45_det `hNu`); case (ii) `1-u < g²/L²` is NOT covered, as in B45_det (record for S3-18a) | `1-u = 1` |
| `Γ` | `2` | `Γ = 2/√κ` | equality |
| `m` | `1` (tensors of `m+2 = 3` indices) | `hY, hF` at rank `m+1 = 2`; `ϑ` at rank `m+2` | n/a |
| `ν, ωf` | `ν = 8`, `ωf = 2` | `1 ≤ ν`, `1 ≤ ωf`, `ωf^{dm} ≤ ν ≤ N` | `ωf^{dm} = 8 = ν` (equality); `ν ≤ N = 2097152` |
| `X` | `1` | `1 ≤ X` | equality |
| `Fv` | `0` | `0 ≤ Fv ≤ ν N^{-(2m+4)} = 9.4e-38` | `Fv` may be anything in `[0, 9.4e-38]` |
| `Λ` | `C = (1+40·dm')·6^{dm'} = 11244096`, `m' = m+1 = 2` | `0 ≤ Λ`; `hϑ`: `‖ϑ u a‖ ≤ Λ (ℓ^d)^{-(m+1)}`; `hϑ'`: `‖∂ϑ‖ ≤ Λ (1-u)⁻¹ (ℓ^d)^{-(m+1)}` | explicit `QopAlgebra_mollifier`: `STMollifierProps` (`Step34Pins.lean:510-515`), `c = 1/2 > 0` so the exponential is `≤ 1`; constants as in `QopAlgebra_mollifier_props` (`QopAlgebra.lean:511`), equality |
| `τN` | `2` | `hMΛ: (2m+5)·3·4^{dm}·Γ·Λ·ν² ≤ N^{τN}` | LHS `1.934e12` ≤ RHS `4.398e12`; slack factor `2.27`, minimal `τN = 1.944` (script) |
| `B` | `3.0987e-5` | `hY: ‖STLKM σ' a'‖ ≤ ν X B^{m+1}` (`= 7.68e-9`) | `STLKM = 0` at this data (below) |
| `ℓ·ωf` | `ℓ = 1`, window `R = 2` | `hF` applies when `ℓ ωf ≤ STdiamInf a'` | rank-2 labels in `Z_4^3`: near (`diam < 2`) 1728, far 2368: both nonempty |
| conclusion 1 | `N^{τN} B^{m+2} X = 0.1309` | `‖𝒫(𝓛-𝒦)_{a₀} ϑ_a‖ ≤ N^{τN}(B^{m+2}X)` (from `B45_det` with `(2m+5)M ≤ N^{τN}`, `M = 3·4^{dm}ΓΛν²`, `(2m+5) ≥ 1`) | trivial at this data (`𝒫 STLKM = 0`); the proof needs only `M ≤ (2m+5) M ≤ N^{τN}` |
| conclusion 2 | `N^{τN} η⁻¹ B^{m+2} X = 0.1309` | `‖altB4N‖ + ‖altB5N‖ ≤ N^{τN}(η⁻¹ B^{m+2} X)` | `η = 1` |
| target 3 | `Y` arbitrary with `‖STLKM σ b‖ ≤ Y` (rank 3) | `‖STQop‖ ≤ Y + N^{τN} B^{m+2} X` via `STQop ϑ u A a = A a - STPsum A (a 0) * ϑ u a` (`Step34Pins.lean:92-94`), `norm_sub_le`, conclusion 1 | no loss beyond conclusion 1 |
| target 4 | `Y ≤ W^{C₀}`, `W = 32` | `‖f‖ = sup_b ‖f b‖ ≤ W^{C₀}`, needs `0 ≤ W^{C₀}` (rpow of `W ≥ 0`) | exact (sup norm of a function on a finite type) |

**Copy table (ticket preflight (i)): every use of `ω` in `B45_det` (`B45.lean:2346`), `B45_det2` (`:2577`), `B45_Psum_LK_le` (`:414`), `B45_ward_fin` (`:200`).**
- `B45_det`/`B45_det2` use `ω` only inside `STLKtensor sz n E u ω ·` (`hY, hF`, the goal, and the call of `B45_Psum_LK_le`). All other tools they call (`B45_scales :2246`, `B45_master_real :530`, `B45_B4_le :862`, `B45_norm_EKsgn :851`, `B45_Psum_le :304`, `B45_Psum_snoc :378`, `B45_norm_kappa :400`) are public and generic in the tensor (grep: 0 `private`).
- `B45_Psum_LK_le`: `ω` only inside `STLKtensor` and the call `B45_ward_fin`.
- `B45_ward_fin`: `ω` enters through (1) `seqHflow_isHermitian sz n u ω` (`FineModel.lean:531`) to be replaced by the hypothesis `H.IsHermitian`, then `.submatrix _`; (2) `B45_Lloop_eq :189`, whose matrix form `STLM sz n E u H σ a = loopL … (blockMat … H) (zt E u) ⟨ofFn σ, ofFn a⟩` is `loopM_eq_loopL` (`GLoopFlow.lean:127`; `STLM = loopFine = loopM ∘ blockMat` by definition, `Step2Defs.lean:60`, `GLoopFlow.lean:110`), with no `ω`. No `SeqΩ` measurability or probability lemma occurs: the "stop and report" condition does not arise.
- **Finding (an addition to the ticket's expectation).** `B45_ward_fin` calls `B45_loopL_ward` (`:107`), which is `private`, with its `private` chain `B45_loopL_eq_prod :78`, `B45_Gres_conj :92`, `B45_loopL_conj :97` (all generic in `H`, no `ω`). These cannot be referenced from `QLevelsA`; they must be copied (about 70 lines, lines `B45.lean:78-150`) under the prefix `QLevelsA_`. Their public inputs: `sum_gloop_ward_last_div` (`ConArgDet.lean:312`), `isUnit_sub_smul_one_of_im_ne_zero` (`:380`), `KLK_ward` (`KLWard.lean:1123`). Mathematics unchanged (Ward identity needs only `H` Hermitian and `Im z ≠ 0`, `z = zt E u`, `Im z = η > 0` for `|E| < 2`, `u < 1`).

**Sign bridge (ticket preflight (ii)).** `EKsgn m σ = fun i => PropSpin m (σ i)` (`Evolution/Pins.lean:45`), `PropSpin m = fun s => if s then m else conj m` (`Propagator/Pins.lean:30`), `mSigma E s = if s then mE E else conj (mE E)` (`Semicircle.lean:85`). So `EKsgn (mE E) σ = fun i => mSigma E (σ i)` after unfolding, same `ite` on `Bool`: expected `rfl`. `altB4N`'s expression (`QDriftA.lean:59-66`) equals `B45_det`'s second conjunct's inner term pointwise (`Pi.sub_apply`), `altB5N a = -(STPsum … (a 0) * deriv …)` (`:71-74`), so `‖altB5N a‖ = ‖STPsum … * deriv …‖` by `norm_neg`. `‖altB4N‖ + ‖altB5N‖` is exactly the second conjunct's left side.

**Consumer lines (§45 O2).**
- S3-18a: `aTrueQN … j = STQop ϑ (gridTime … j) (AvecN …)` (`QGridA.lean:1263-1266`) at `j = 0` is target 3 at `u = gridTime … 0 = s` (`ST_gridTime_zero`, used at `NQLin.lean:857`), `H = H_0`, `Y` the current-length level. Crude-sup binders of `alt_hDclsQN` (`QDriftB.lean:395-402`) and `goodSetN_A0clsQN` have the form `‖fun b : Fin (m+1) → Zd d (sz.L n) => sz.STLKM n (E n) (gridTime …) (pathH …) σ b‖ ≤ W^{C₀}`, which is target 4 at `k = m+1`.
- S3-16b: target 2 at `u = u_j`, `H = H_j` Hermitian (clause 1 of `GoodSetN`, `GridGoodN.lean:126`).
- External hypothesis: none (every hypothesis of targets 2-4 is a norm bound, an inequality or `IsHermitian`; no pin `Prop`), so no limit computation is owed. The eventual numerical facts (`L^d ≤ W^K` etc.) belong to S3-18a and are not hypotheses here.

### (ii) One concrete nondegenerate instance

Data: `d = 3`, `sz0` (`Defs/Sizes.lean:260`) at `n = 0` (`L = 4, W = 32, lam = 1/64, N = 2097152`), `E = 0`, `κ = 1`, `u = 0`, `m = 1`, `H = 0` (Hermitian), `σ = (+,+,-)` (`σ_last = ¬σ_0`), `ϑ = QopAlgebra_mollifier 3 4 2 lam`, `Λ = 11244096`, rank-3 labels, `Y = 1`, `C₀ = 1`.
Why `hY, hF` hold: at `H = 0`, `E = 0`, `u = 0`: `z = zt 0 0 = i` (`mE 0 = (0 + 2i)/2 = i`, `ztOf m E t = E + (1-t) m`), `Gres 0 z σ = m(σ)·I` (`m(+) = i`, `m(-) = -i`), `E_a = W^{-d}·1_{block a}` (`GLoop.lean:55`), so `𝓛^{(k)}_{σ,a} = ∏ m(σ_i) W^{-d(k-1)} 1[a const]` (toy check below). On the `𝒦` side: `KLgen` rank 1 `= m(σ)`; rank 2 `kTwo = W^{-d} m₁m₂ Theta 0`, `Theta 0 = 1` (`Theta_zero`, `Primitive.lean:51`); rank `≥ 3` `KLn = ∏m · W^{-d(k-1)} Σ_{F ∈ TSP} Γ_F` with `thetaEdge = Theta 0 = 1`, so edges `Θ - 1 = 0` kill every `F ≠ ∅` and `∅ ∈ TSP` (`empty_mem_TSP`) gives `1[a const]`. Hence `STLKM n 0 0 0 σ a = 0` for all ranks, so `hY` holds (RHS `7.68e-9 > 0`) and `hF` holds with `Fv = 0`; the far set is nonempty (2368 of 4096 rank-2 labels), the near set too (1728). The mathematics of the hypotheses `hY, hF` is therefore not vacuous in the label sense; the entries are zero because `H = 0 = H_{u=0}` is the exactly-solved point.
Target 3 at the same data: `Y = 1`, hypothesis `‖STLKM σ b‖ = 0 ≤ 1`, conclusion `‖STQop‖ ≤ 1 + 0.1309`. Target 4: `k = 3`, `Y = W^{1} = 32`, `‖STLKM σ b‖ = 0 ≤ 32`, `Y ≤ W^{C₀}` with `C₀ = 1`. Label type `Fin 3 → Zd 3 4` has `4^9` elements.

Command and output:
```
python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2268/inst.py
L,W,N,lam 4 32 2097152 0.015625
0<kappa, |E|<=2-kappa: True True  0<=u<1: True  lam>0: True  1/N<=1-u: True
eta,ell,Bctl 1.0 1 3.0986966521151624e-05
1<=nu,X,omf: True True True  omf^(dm)<=nu<=N: 8.0 8.0 2097152 True
Fv<=nu*N^-(2m+4): True   nu*N^-6 = 9.4039548065783e-38  Fv>=0, Lam>=0: True True
hMLam: (2m+5)*3*4^(dm)*Gam*Lam*nu^2 = 1934344323072.0  <= N^tauN = 4398046511104.0 True  slack 2.273662686961186  min tauN = 1.9435705601588409
hY level nu*X*Bctl^(m+1) = 7.681536753463772e-09  (STLKM=0 at H=0,u=0,E=0, see toy check)
conclusion level N^tau*(Bctl^(m+2)*X) = 0.13085701420062013 ; B4+B5 level N^tau*eta^-1*Bctl^(m+2)*X = 0.13085701420062013
window R=ell*omf = 2.0 : rank-2 labels near(diam<R) = 1728  far(diam>=R) = 2368  both nonempty: True
toy (d=1,L=3,W=2) loops at H=0, z=i equal prod m_s W^{-d(k-1)} delta_{a const} for k=1..4: True
```

### Verdicts

- Target 1 (private copies `QLevelsA_ward_finM`, `QLevelsA_Psum_LK_leM`, plus the private chain `QLevelsA_loopL_eq_prod/_Gres_conj/_loopL_conj/_loopL_ward`): PASS. The extra private chain is a finding, not a blocker (generic in `H`).
- Target 2 (`altB45N_levelM`): PASS. Hypotheses are those of `B45_det2` verbatim with `STLKM … H` for `STLKtensor … ω`; instance above satisfies all (slack table).
- Target 3 (`startLevelQN`): PASS (`norm_sub_le` plus conclusion 1; no new exponent).
- Target 4 (`crudeLKM_of_level`): PASS (`pi_norm_le_iff_of_nonneg` with `0 ≤ W^{C₀}`).
- Paper-delta candidate expected: `T2268a` (per-matrix deterministic levels, §62 (4)), as the ticket says.

## (b) Script output — stage 1b, Tue Oct  6 07:50 UTC 2026 (branch `t/T2268`, commit 5839c77)

### Build, axioms, registry pre-check, statement script (commands and verbatim output)
Scripts (scratchpad `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2268/`): `extract.py`, `stmt_check.lean`, `axioms.lean`, `registry.lean`, `names.lean`.
```
$ lake build RBM3D.Induction.QLevelsA 2>&1 | tail -3

Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3857 jobs).

$ lake env lean axioms.lean   # import RBM3D.Induction.QLevelsA; #print axioms <six public declarations>
'RBM.Ind.altB45N_levelM' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.startLevelQN' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.crudeLKM_of_level' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QLevelsAInst.altB45N_levelM_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QLevelsAInst.startLevelQN_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QLevelsAInst.crudeLKM_of_level_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0

$ lake env lean registry.lean   # import RBM3D; import RBM3D.Induction.QLevelsA; #assert_rbm_axioms
exit=0
axiom audit: 7789 theorems, 2578 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
non-vacuity certificates: 0 of 157 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)

$ lake env lean stmt_check.lean   # check file + import QLevelsA + three `example : RBM.Ind.T2268Check.T2268_x := @RBM.Ind.x`
exit=0
0

$ grep -n -E "sorry|admit|native_decide|maxHeartbeats|^axiom" RBM3D/Induction/QLevelsA.lean | wc -l
       0

$ git diff --name-only main...t/T2268
RBM3D/Induction/QLevelsA.lean

$ wc -l RBM3D/Induction/QLevelsA.lean
     687 RBM3D/Induction/QLevelsA.lean
```

### Target statements, extracted from `RBM3D/Induction/QLevelsA.lean` by `extract.py` (whitespace-normalised)
```
theorem altB45N_levelM (d : ℕ) (hd : 2 ≤ d) (sz : Sizes d) (n : ℕ) (E u κ : ℝ) (hκ : 0 < κ)
 (hE : |E| ≤ 2 - κ) (hu0 : 0 ≤ u) (hu1 : u < 1) (hg : 0 < sz.lam n)
 (hNu : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - u)
 (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hH : H.IsHermitian)
 (m : ℕ) (Γ ν X ωf Fv Λ τN : ℝ) (hΓ : Γ = 2 / Real.sqrt κ) (hν : 1 ≤ ν) (hX : 1 ≤ X)
 (hωf : 1 ≤ ωf) (hωd : ωf ^ (d * m) ≤ ν) (hνN : ν ≤ ((sz.size n : ℕ) : ℝ))
 (hFv : Fv ≤ ν * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹) (hFv0 : 0 ≤ Fv) (hΛ : 0 ≤ Λ)
 (hMΛ : (2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τN)
 (hY : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
 ‖sz.STLKM n E u H σ' a'‖ ≤ ν * X * sz.Bctl n u ^ (m + 1))
 (hF : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
 ellT (sz.L n) (sz.lam n) u * ωf ≤ (STdiamInf a' : ℝ) → ‖sz.STLKM n E u H σ' a'‖ ≤ Fv)
 (ϑ : ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ)
 (hϑ : ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
 ‖ϑ u a‖ ≤ Λ * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1)))
 (hϑ' : ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n), ‖deriv (fun t : ℝ => ϑ t a) u‖ ≤
 Λ * (1 - u)⁻¹ * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1)))
 (σ : Fin (m + 1 + 1) → Bool) (hσ : σ (Fin.last (m + 1)) = !σ 0)
 (a : Fin (m + 1 + 1) → Zd d (sz.L n)) :
 ‖STPsum (d := d) (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => sz.STLKM n E u H σ b) (a 0) *
 ϑ u a‖ ≤
 ((sz.size n : ℕ) : ℝ) ^ τN * (sz.Bctl n u ^ (m + 2) * X) ∧
 ‖altB4N sz n E u ϑ σ H a‖ + ‖altB5N sz n E u ϑ σ H a‖ ≤
 ((sz.size n : ℕ) : ℝ) ^ τN * ((etaT E u)⁻¹ * sz.Bctl n u ^ (m + 2) * X)

theorem startLevelQN (d : ℕ) (hd : 2 ≤ d) (sz : Sizes d) (n : ℕ) (E u κ : ℝ) (hκ : 0 < κ)
 (hE : |E| ≤ 2 - κ) (hu0 : 0 ≤ u) (hu1 : u < 1) (hg : 0 < sz.lam n)
 (hNu : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - u)
 (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hH : H.IsHermitian)
 (m : ℕ) (Γ ν X ωf Fv Λ τN Y : ℝ) (hΓ : Γ = 2 / Real.sqrt κ) (hν : 1 ≤ ν) (hX : 1 ≤ X)
 (hωf : 1 ≤ ωf) (hωd : ωf ^ (d * m) ≤ ν) (hνN : ν ≤ ((sz.size n : ℕ) : ℝ))
 (hFv : Fv ≤ ν * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹) (hFv0 : 0 ≤ Fv) (hΛ : 0 ≤ Λ)
 (hMΛ : (2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τN)
 (hY : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
 ‖sz.STLKM n E u H σ' a'‖ ≤ ν * X * sz.Bctl n u ^ (m + 1))
 (hF : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
 ellT (sz.L n) (sz.lam n) u * ωf ≤ (STdiamInf a' : ℝ) → ‖sz.STLKM n E u H σ' a'‖ ≤ Fv)
 (ϑ : ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ)
 (hϑ : ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
 ‖ϑ u a‖ ≤ Λ * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1)))
 (σ : Fin (m + 1 + 1) → Bool) (hσ : σ (Fin.last (m + 1)) = !σ 0)
 (hYtop : ∀ b : Fin (m + 1 + 1) → Zd d (sz.L n), ‖sz.STLKM n E u H σ b‖ ≤ Y)
 (a : Fin (m + 1 + 1) → Zd d (sz.L n)) :
 ‖STQop (d := d) ϑ u (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => sz.STLKM n E u H σ b) a‖ ≤
 Y + ((sz.size n : ℕ) : ℝ) ^ τN * (sz.Bctl n u ^ (m + 2) * X)

theorem crudeLKM_of_level (d : ℕ) (sz : Sizes d) (n : ℕ) (E u : ℝ)
 (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (k : ℕ) (σ : Fin k → Bool)
 (Y C₀ : ℝ) (hY : ∀ b : Fin k → Zd d (sz.L n), ‖sz.STLKM n E u H σ b‖ ≤ Y)
 (hW : Y ≤ ((sz.W n : ℕ) : ℝ) ^ C₀) :
 ‖fun b : Fin k → Zd d (sz.L n) => sz.STLKM n E u H σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀

```
Pin comparison: `stmt_check.lean` is the check file `docs/tickets/checks/T2268-check.lean` plus `import RBM3D.Induction.QLevelsA` and the three lines
`example : T2268Check.T2268_altB45N_levelM := @RBM.Ind.altB45N_levelM` (same for `startLevelQN`, `crudeLKM_of_level`); it compiles with exit 0 and 0 `error` lines (above), so each theorem has exactly the pinned statement.

### Compiled nonempty instances (`RBM.Ind.QLevelsAInst`, same file; statements extracted by script)
Data: `sz0` (`d = 3`), `n = 0` (`L = 4`, `W = 32`, `lam = 1/64`, `N = 2097152`), `m = 1`, `E = 0`, `u = 0`, `κ = 1` (`Γ = 2`), `H = 0`, `ν = 8`, `ωf = W^{1/5} = 2`, `X = 1`, `Fv = W^{-36}`, `τN = 2`, `ϑ = QopAlgebra_mollifier 3 L 2 lam`, `Λ = (1+40·6)·6^6 = 11244096`.
```
theorem altB45N_levelM_instance (σ : Fin (1 + 1 + 1) → Bool) (hσ : σ (Fin.last (1 + 1)) = !σ 0)
 (a : Fin (1 + 1 + 1) → Zd 3 (sz0.L 0)) :
 (∃ b : Fin (1 + 1) → Zd 3 (sz0.L 0), ellT (sz0.L 0) (sz0.lam 0) 0 * 2 ≤ (STdiamInf b : ℝ)) ∧
 ‖STPsum (d := 3) (fun b : Fin (1 + 1 + 1) → Zd 3 (sz0.L 0) => sz0.STLKM 0 0 0 H0 σ b) (a 0) *
 QopAlgebra_mollifier 3 (sz0.L 0) 2 (sz0.lam 0) 0 a‖ ≤
 ((sz0.size 0 : ℕ) : ℝ) ^ (2 : ℝ) * (sz0.Bctl 0 0 ^ (1 + 2) * 1) ∧
 ‖altB4N sz0 0 0 0 (QopAlgebra_mollifier 3 (sz0.L 0) 2 (sz0.lam 0)) σ H0 a‖ +
 ‖altB5N sz0 0 0 0 (QopAlgebra_mollifier 3 (sz0.L 0) 2 (sz0.lam 0)) σ H0 a‖ ≤
 ((sz0.size 0 : ℕ) : ℝ) ^ (2 : ℝ) * ((etaT 0 0)⁻¹ * sz0.Bctl 0 0 ^ (1 + 2) * 1)

theorem startLevelQN_instance (σ : Fin (1 + 1 + 1) → Bool) (hσ : σ (Fin.last (1 + 1)) = !σ 0)
 (a : Fin (1 + 1 + 1) → Zd 3 (sz0.L 0)) :
 ‖STQop (d := 3) (QopAlgebra_mollifier 3 (sz0.L 0) 2 (sz0.lam 0)) 0
 (fun b : Fin (1 + 1 + 1) → Zd 3 (sz0.L 0) => sz0.STLKM 0 0 0 H0 σ b) a‖ ≤
 (4 * 1 - 1) * sz0.Bctl 0 0 ^ (1 + 1 + 1) +
 ((sz0.size 0 : ℕ) : ℝ) ^ (2 : ℝ) * (sz0.Bctl 0 0 ^ (1 + 2) * 1)

theorem crudeLKM_of_level_instance (σ : Fin (1 + 1 + 1) → Bool) :
 ‖fun b : Fin (1 + 1 + 1) → Zd 3 (sz0.L 0) => sz0.STLKM 0 0 0 H0 σ b‖ ≤
 ((sz0.W 0 : ℕ) : ℝ) ^ (1 : ℝ)

```
Every deterministic hypothesis is discharged inside the proof terms: `hY` and `hYtop` from clause (G2) of `0 ∈ GoodSetN` (`zero_mem_goodSetN_of_levels`, `AzumaProxyN.lean:924`, levels `(4,100,1)`, `k = 4`, `τ' = 1/5`, `D' = 36`) through the private `norm_STLKM_le_of_XiLKM`; `hF` from clause (Dec); `hϑ`, `hϑ'` from `QopAlgebra_mollifier_props` (`exp ≤ 1` for `c = 1/2`); `hMΛ0`, `hFv0'`, `hNu0` by `norm_num` at the numbers above. Instance statements are `∀ σ` alternating and `∀ a`. The far window of `hF` (`ℓ_0 ωf = 2 ≤ diam_∞`) is attained (`window0`, conjunct 1 of the first instance), so `hF` is not vacuous. No `N = 0`, no empty index set.

### Name-clash grep and port citations
```
$ (main worktree /Users/junyin/Lean_proof/RBM3D) grep -rn -F -e altB45N_levelM -e startLevelQN -e crudeLKM_of_level -e QLevelsA -e B45_ward_finM RBM3D RBM3D.lean | wc -l
       0
$ (branch) the same grep, files only:  RBM3D/Induction/QLevelsA.lean
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h
9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Induction/AltLevelsQ0.lean | tail -2
 RBM2D/Induction/AltLevelsQ0.lean | 108 ++++++------------------------
 1 file changed, 20 insertions(+), 88 deletions(-)
```
Ports: no text is copied from RBM1D/RBM2D (RBM2D `AltLevelsQ0.lean:55-64, 380-522` at `c9a24cf`, read with `git show`, is the pattern of target 3 only). The Lean text is copied from merged RBM3D files (read-only here): `RBM3D/Induction/B45.lean` at `1ef8fa7` (`git log --oneline -1 main -- RBM3D/Induction/B45.lean`; diff-stat `1ef8fa7..main` of that file is empty): private chain `B45_loopL_eq_prod/_Gres_conj/_loopL_conj/_loopL_ward` `:78-149`, `B45_ward_fin` `:200`, `B45_Psum_LK_le` `:414`, `B45_det` `:2346-2438`, `B45_det2` `:2603-2635`; instance helpers `ellT0`, `window0` follow `QDriftB.lean:533-590` (`c01b292`).

### Narrative
File `RBM3D/Induction/QLevelsA.lean`, 687 lines, the only file in `git diff --name-only main...t/T2268`; `RBM3D/Test/Axioms.lean` untouched (no public theorem takes a new `Prop`; registry pre-check exit 0). Full `lake build` run in the worktree at 07:4x UTC, before the final deletion of an unused private lemma (`RBM3D.lean` does not yet import `QLevelsA`, the hub adds the import at merge): `Build completed successfully (4074 jobs)`; the module build above is after that deletion. No `maxHeartbeats` option, no `sorry`.
Layout: §1 (lines 46-199) private chain and the two copies of target 1; §2 (201-410) `QLevelsA_PiM`, `QLevelsA_absorb`, `QLevelsA_detM`, then `altB45N_levelM` (target 2); §3 `startLevelQN` (412-455); §4 `crudeLKM_of_level` (457-468); §5 instances (470-683).
Target 1 (private): `QLevelsA_ward_finM` and `QLevelsA_Psum_LK_leM` are `B45_ward_fin`/`B45_Psum_LK_le` with `sz.STLKM n E u H` for `STLKtensor sz n E u ω` and `hH : H.IsHermitian` for `seqHflow_isHermitian`; the `Lloop` bridge is `loopM_eq_loopL` (`STLM = loopFine`, by `rfl`). As the preflight (a) found, `B45_loopL_ward` and its chain are `private` in `B45.lean`, so I copied them as `QLevelsA_loopL_eq_prod/_Gres_conj/_loopL_conj/_loopL_ward` (generic in `H`, no `ω`). Public name `B45_ward_finM` not introduced (no sibling needs it yet).
Target 2: `QLevelsA_detM` is `B45_det` at `H`; its second conjunct is stated on `altB4N`, `altB5N`: `ℬ₄` by `B45_B4_le` (`hμ` is `B45_norm_EKsgn` for `fun i => mSigma E (σ i)`, accepted by `rfl`-defeq, so no `funext` lemma was needed), `ℬ₅` by `norm_neg`. `altB45N_levelM` is `B45_det2`'s absorption `(2m+5)M ≤ N^τ`.
Deviation from the ticket's plan (not from a pin): target 3 has no `hϑ'` hypothesis, so it cannot call `altB45N_levelM`. I split the `𝒫`-bound and exponent count into the private `QLevelsA_PiM` and the absorption into `QLevelsA_absorb`; `QLevelsA_detM`, `altB45N_levelM`, `startLevelQN` all use them. Target 3 is then `norm_sub_le` on `STQop = A a - STPsum A (a 0) * ϑ u a` (by `rfl`).
Target 4: `pi_norm_le_iff_of_nonneg` with `0 ≤ W^{C₀}` (`Real.rpow_nonneg`).
Section (a) is not edited and there is no (a′): none of its verdicts changes. The instance differs from (a)'s only in how the levels are discharged: (a) argues `STLKM = 0` at `H = 0`; Lean takes `hY`, `hF` from the merged `0 ∈ GoodSetN` (levels `(4,100,1)`), which gives `‖STLKM‖ ≤ 3B^j` and `≤ W^{-D'}`; the numbers `ν = 8`, `ωf = 2`, `X = 1`, `Λ = 11244096`, `τN = 2`, `N = 2097152` are those of (a)'s table, and `Fv = W^{-36} = 32^{-36}` lies in (a)'s range `[0, 9.4e-38]`.

## (c) Verified Mathlib names (all `#check`ed in `names.lean`, exit 0; none checked and found absent)
```
pi_norm_le_iff_of_nonneg : ∀ {ι : Type u_1} {G : ι → Type u_2} [inst : Fintype ι]
Real.rpow_nonneg : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), 0 ≤ x ^ y
Real.pow_rpow_inv_natCast : ∀ {x : ℝ} {n : ℕ}, 0 ≤ x → n ≠ 0 → (x ^ n) ^ (↑n)⁻¹ = x
Real.rpow_neg : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), x ^ (-y) = (x ^ y)⁻¹
Real.rpow_natCast : ∀ (x : ℝ) (n : ℕ), x ^ ↑n = x ^ n
Real.rpow_two : ∀ (x : ℝ), x ^ 2 = x ^ 2
Real.rpow_one : ∀ (x : ℝ), x ^ 1 = x
Real.exp_le_one_iff : ∀ {x : ℝ}, Real.exp x ≤ 1 ↔ x ≤ 0
Finset.le_sup' : ∀ {α : Type u_1} {β : Type u_2} [inst : SemilatticeSup α] {s : Finset β} (f : β → α) {b : β}
Finset.le_sup : ∀ {α : Type u_1} {β : Type u_2} [inst : SemilatticeSup α] [inst_1 : OrderBot α] {s : Finset β}
Finset.sup_const : ∀ {α : Type u_1} {β : Type u_2} [inst : SemilatticeSup α] [inst_1 : OrderBot α] {s : Finset β},
div_nonpos_of_nonpos_of_nonneg : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀]
div_le_iff₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [MulPosReflectLT G₀] {a b c : G₀},
norm_sub_le : ∀ {E : Type u_1} [inst : SeminormedAddGroup E] (a b : E), ‖a - b‖ ≤ ‖a‖ + ‖b‖
norm_neg : ∀ {E : Type u_1} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ = ‖a‖
ZMod.val_natCast : ∀ (n a : ℕ), (↑a).val = a % n
Matrix.isHermitian_zero : ∀ {α : Type u_1} {n : Type u_2} [inst : AddMonoid α] [inst_1 : StarAddMonoid α],
Matrix.IsHermitian.submatrix : ∀ {α : Type u_1} {m : Type u_2} {n : Type u_3} [inst : Star α] {A : Matrix n n α},
Complex.conj_conj : ∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : StarRing R] (x : R),
inv_anti₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀]
Real.sqrt_one : √1 = 1
```

## (d) Open issues and paper-delta candidates
1. `T2268a`: the start level `3_5:1676-1690` and `(y27kasdfg)` hold per matrix from deterministic rank-`(m+1)` levels (`hY`, `hF`), the mollifier bounds and `H.IsHermitian` alone (`altB45N_levelM`, `startLevelQN`); no `≺`, no good set, no lift is needed before the assembly (§62 (4), §64 (4)). `AltLevelsE` is not ported (§83).
2. `T2268b`: only case (i) `N⁻¹ ≤ 1 - u` (`hNu`) is covered, exactly as `B45_det`; case (ii) `1 - u < g²/L²` is not. For S3-18a: `STOeqQt′` is `STIngR d STCaseI …`, so case (i) is expected to suffice; if not, a case (ii) successor is needed.
3. `T2268c` (cleanup, not a defect): target 2 duplicates `B45_det`/`B45_Psum_LK_le`/`B45_ward_fin` (about 250 lines) because `B45.lean` is not writable. A later cleanup can restate `B45_det` via `altB45N_levelM`, since `STLKtensor sz n E u ω = fun a => sz.STLKM n E u (sz.seqHflow n u ω) σ a` by `rfl`.
4. Consumer lines (§45 O2): S3-18a uses `startLevelQN` at `u = gridTime … 0 = s` (`ST_gridTime_zero`), `H = H_0`, with `Y` the current-length level, and `crudeLKM_of_level` for the `hcrude` binders of `alt_hA0clsQN`/`goodSetN_A0clsQN`/`alt_hDclsQN`; S3-16b uses `altB45N_levelM` at `u = u_j`, `H = H_j` Hermitian (clause 1 of `GoodSetN`). The hypotheses `hY`, `hF` are the deterministic levels those tickets must supply; the numerical side conditions of T2263 (d) 2 (`L^d ≤ W^K`, etc.) are not hypotheses here.
5. The explicit-mollifier instance took about 25 lines (`moll_sup`, `moll_deriv`), under the ticket's 80-line limit, so it is included. `Λ` is the constant of `QopAlgebra_mollifier_props` (not `ϑ ≡ 0`).
6. Per-matrix instance values: at `H = 0` the actual entries of `(𝓛-𝒦)` vanish ((a), toy check), so the conclusions hold with room; the instance tests the hypotheses and the application, not tightness of the levels.
