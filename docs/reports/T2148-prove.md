Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 17:47:48 UTC 2026

### (i) Exponent table

Notation (merged defs): `X := STLKM … σ = 𝓛−𝒦` (`Induction/Step2Defs.lean:68`), `Q := zeroModeSet d L {0}` = `I − avg over index 0` (`Kernel/Evolution.lean:190-201`, `avgOp = (L^d)⁻¹ Σ_c`), so `X − Q X = P X`, `(P X)(a₁,a₂) = L^{-d} Σ_{c} X(c,a₂)`. `N = (WL)^d = sz.size`, `η_u = (1−u) Im m(E)` (`Loop/GLoop.lean:75`), `E_a = diag(1_{x∈[a]}) W^{-d}` (`Loop/GLoop.lean:55`), `A = λ²W^d` (`STAI`, `Step34Pins.lean:79`), `W^{-d}B_{u,0} = Bctl` (`Defs/Sizes.lean:214`), `Bparam d L g u 0 = (g²+|1−u|)⁻¹ + (L^d|1−u|)⁻¹` (`Defs/Params.lean:36`, `K=0`, `(0+1)^{d−2}=1`).

| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | Ward sum for `𝓛` over the FIRST index, `σ=(+,−)` and `σ=(−,+)` | `Σ_{a₁}𝓛^{(2)}_{σ,(a₁,a₂)} = Im𝓛^{(1)}_{+,a₂}/(W^d η_u)` (`Σ_{a₁}E_{a₁}=W^{-d}I`), sign `+` for BOTH `σ` (`G G* = G*G = Im G/η`; `tr(E_a ImG)=Im tr(E_aG)`, `E_a` real diagonal) | exact identity, every Hermitian `H`, `z=zt E u`, `Im z>0` | equality; `sum_gloop_two_ward` (`ConArgDet.lean:235`) sums the SECOND index, first index by trace cyclicity |
| 2 | Ward sum for `𝒦` | `Σ_{a₁}𝒦^{(2)}_{σ,(a₁,a₂)} = Im 𝒦^{(1)}_{+,a₂}/(W^dη_u)`, both `σ` | `KLK_ward` (`Loop/KLWard.lean:1123`, sum over the LAST index, `σ=(s,!s)`, `s=±`) + `KLK_rotate` (`Loop/KLUnique.lean:604`: `𝒦_{s::σ,b::a}=𝒦_{σ++[s],a++[b]}`) + `KLK_one`: `𝒦^{(1)}_± = m, m̄` | equality; hypotheses `3≤L, 1≤W, |E|<2, 0≤u<1` |
| 3 | prefactor of the pin | `L^{-d}·(W^dη_u)⁻¹ = (Nη_u)⁻¹`, `N=(WL)^d=sz.size n` | must equal pin's `((sz.size n : ℕ) * etaT (E n) u)⁻¹` | equality (no factor 2, no `W^d` vs `N` mismatch) |
| 4 | sign / zero-mode convention | `X − QX = +Im X^{(1)}_{+,a₂}/(Nη_u)` for `σ=(+,−)` and `(−,+)` | the ticket's "±" is `+` in both cases; `{0}` = first index, matches `Σ_{a₁}` | numeric: `+` sign error 6e-17, `−` sign error 6.2e-2 (vs size 1.8e-2), see (ii) |
| 5 | `Im(𝓛−𝒦)^{(1)}` size | `|Im X^{(1)}_{+,a₂}| ≤ |X^{(1)}_{+,a₂}| ≺ Bctl` | `STAvgU` (`Step34Pins.lean:192`, uniform in `u∈[s,t]`, `k=1`, `σ=(+)`, `a=(a₂)`) | no loss exponent; deterministic factor `(Nη_u)⁻¹>0` carries through `Prec` (`StochDomAt`, `Defs/StochDomAt.lean:61`: `∀τ>0 ∀D>0 ∀ᶠ n`, constant `2 ≤ N^τ` eventually) |
| 6 | `Bctl ≤ 2 A⁻¹` in regime (ii) | `Bparam(u,0) ≤ (g²)⁻¹ + (g²)⁻¹ = 2g⁻²` since `1−u ≥ 1−t ≥ g²/L^d` (`STReg5II`, `Step5Pins.lean:48`; `u ≤ t`) and `g²+x ≥ g²`; `W^{-d}·2g⁻² = 2A⁻¹` (the same computation is a local `have hBv` at `ScaleFacts3.lean:348`, not a named lemma; a new private `wardII_` lemma is needed) | `g=sz.lam n>0`, `1−u>0`; upper window `1−s ≤ g²/L²` NOT used | sup over `x ≥ g²/L^d` of `g²Bparam(u,0)` is at `x=g²/L^d`: `1 + 1/(1+L^{-d})`; slack to 2 is `1/(L^d+1)` (`L=3,d=3`: 1/28 = 0.0357; `L=4`: 1/65) |
| 7 | constant of the final comparison | `‖X−QX‖ = |ImX^{(1)}|/(Nη_u) ≺ Bctl/(Nη_u) ≤ 2A⁻¹(Nη_u)⁻¹` | pin target `A⁻¹(Nη_u)⁻¹` | factor 2 absorbed by `N^τ` (`τ>0`, eventually) |
| 8 | side conditions of the deterministic identity | `|E|<2` (`abs_lemE_lt_two`, from `Im z_n>0`, `locDomain` `Defs/Sizes.lean:186`), `u<1` (`st5_t_lt_one`, `Step5Kit.lean:191`), `0≤s n` (hypothesis of `STIngR5`), `3≤L` (`sz.three_le_L`), `1≤W` (`sz.W_pos`), `Im z_u=η_u>0` | all provided by `STFlow` + `STReg5II` | `λ>0` needed only for `1−u>0` in row 6: `st5_eventually_A_ge_one` (`Step5Kit.lean:200`) gives `0<λ ∧ 1≤A` eventually, enough because `Prec` is `∀ᶠ n` |

(iii) Which `STIngR5` hypothesis supplies `STAvgU`: `STIngR5` (`Step5Pins.lean:82`) lists `STStep2Concl sz (STflowE z) s t Cd`; `STStep2Concl := STLocalEntryU ∧ STAvgU ∧ STGdecayW Cd` (`Step34Pins.lean:221`), so `STAvgU = (hStep2).2.1`. The hypothesis `STLKU` at `k=1` has the identical body  and also works. `STKbound`, `STKward`, `STLK`, `STDecay*`, `STConStInd`, `STStep1Loop`, `STLmaxU` are not needed (the Ward identities are deterministic).

### (ii) Concrete nondegenerate instance

Identity (targets 1): `d=3, L=3, W=1` (`N=27`), `λ=g=1`, `E=1/2`, `u=1/2`, random Hermitian `27×27 H` (seed 1), `𝒦^{(2)}` computed from `KLK_two` (`Loop/KLTree.lean:211`: `W^{-d} m₁m₂ Θ_{u m₁m₂}(a₁,a₂)`, `Θ=(1−ξS^B)⁻¹`, `S^B` from `Defs/Block.lean:39-44`), `𝒦^{(1)}_±=m(E), m̄(E)`, `𝓛` as in `loopM` (`tr ∏ G_{σ_i}E_{a_i}`, `G_−=(H−z̄)⁻¹`, `z=E+(1−u)m(E)`). All 27 values of `a₂` and both `σ` are checked; also `KLK_ward` (both `s`) and the cyclic rotation of `𝒦`.

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2148/ward2.py`
Output:
```
SB row sum [1. 1.]
sigma (True, False) max|lhs-(+Im/(N eta))|=6.26e-17 max|lhs-(-Im/(N eta))|=6.18e-02 L-part 4.17e-17 K-part 8.33e-17
sigma (False, True) max|lhs-(+Im/(N eta))|=6.58e-17 max|lhs-(-Im/(N eta))|=6.18e-02 L-part 3.48e-17 K-part 8.33e-17
N= 27 eta= 0.4841229182759271 |rhs| scale 0.018205247857756974 Im L1= 0.7302792380893396
KLK_ward s= True err 2.22e-15
KLK_ward s= False err 2.22e-15
K cyc err 1.39e-16
```
(`lhs = X(σ,(a₁,a₂)) − (QX)(σ,(a₁,a₂))`, `rhs = Im X^{(1)}_{+,a₂}/(Nη_u)`; `η_u=0.4841`, `|rhs|` about `1.8e-2`, so the `−` test at 6e-2 discriminates the sign.)

Chain (targets 2): data `(szB, s=15/16, t=31/32)` (`Step34Pins.lean:710`, `Step5Pins.lean:517`): `d=3, L=4, W_n=n+4, λ=1`; regime (ii) holds with `1−s=g²/L²` (boundary) and `1−t=1/32 ≥ g²/L^d=1/64`. The script uses exact rationals; `Bctl·A ≤ 2` is the claim `Bctl ≤ 2A⁻¹`.

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2148/chain.py`
Output:
```
regime (ii): lam^2/L^d = 1/64 <= 1-t = 1/32 ; 1-s = 1/16 <= lam^2/L^2 = 1/16 True
W=4 A=64  max_u Bctl*A = 1.4697 (<=2: True)  A>=1: True
W=5 A=125  max_u Bctl*A = 1.4697 (<=2: True)  A>=1: True
W=14 A=2744  max_u Bctl*A = 1.4697 (<=2: True)  A>=1: True
lam=1 L=3 x=lam^2/L^3: Bparam(u,0)*lam^2 = 1.96429 <= 2
lam=1/2 L=4 x=lam^2/L^3: Bparam(u,0)*lam^2 = 1.98462 <= 2
lam=2 L=5 x=lam^2/L^3: Bparam(u,0)*lam^2 = 1.99206 <= 2
lam=1/10 L=10 x=lam^2/L^3: Bparam(u,0)*lam^2 = 1.99900 <= 2
```
The last four lines are the left edge `1−u = g²/L^d` for other `(λ,L)`: values `1+1/(1+L^{-3})` (`L=3`: 1.96429 = 1+27/28), below 2.

External hypotheses: none are introduced. The only non-deterministic input is `STAvgU`, a hypothesis already inside `STIngR5` (via `STStep2Concl`), not a new one. Limit check at `szB` (`A=W^3→∞`, `N=(4W)^3→∞`, `1−u ≥ 1/32`): the pin's bound satisfies `A⁻¹(Nη_u)⁻¹ ≤ 32/(Im m(E)) · A⁻¹N⁻¹ → 0`, positive for every `n`, and the supplied scale is `Bctl ≤ 1.4697/A` (chain output above).

### Verdicts

- Target 1 (identity `STLKM σ a − zeroModeSet {0} (STLKM σ) a = +Im((𝓛−𝒦)^{(1)}_{u,+,a₂})/(Nη_u)`, both `σ∈{(+,−),(−,+)}`): PASS. Sign is `+` for both `σ` (the ticket's "±" resolves to `+`); proof route: first-index Ward for `𝓛` (trace cyclicity applied to `sum_gloop_two_ward`'s argument), `KLK_ward`+`KLK_rotate`+`KLK_one` for `𝒦`.
- Target 2 (`stWardII_holds d : STWardII d`): PASS. The pin is true as stated (sign, `N=(WL)^d`, `A⁻¹` factor, index set `STIdx2P STSigMixed`); constant 2 from row 6 is absorbed by `≺`.

## (b) Script output

```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2148 && git log -1 --format=%h; git diff --stat main...t/T2148
bf8a55b
 RBM3D/Induction/WardII.lean | 364 ++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean      |   1 -
 2 files changed, 364 insertions(+), 1 deletion(-)

$ lake build RBM3D.Induction.WardII RBM3D.Test.Axioms   (tail)

Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3778 jobs).

$ lake env lean ax.lean   (#print axioms of both public declarations)
'RBM.Gauss.Sizes.stWardII_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stWardII_holds' depends on axioms: [propext, Classical.choice, Quot.sound]

$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/Induction/WardII.lean ; echo rc=$?
rc=1

$ registry pre-check: lake env lean Precheck.lean   (import RBM3D; import RBM3D.Induction.WardII; #assert_rbm_axioms; STWardII line deleted from RBM3D/Test/Axioms.lean)
exit 0; head of output:
axiom audit: 4503 theorems, 1606 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
error lines: 0

$ full lake build with the root import line added TEMPORARILY to RBM3D.lean (restored afterwards; git status shows RBM3D.lean unmodified)
exit 0:
lake build  15.53s user 4.45s system 112% cpu 17.810 total
1836:Build completed successfully (3896 jobs).
without the root import, `lake build` stops at the root audit: "axiom audit: 1 premise(s) ... [RBM.Gauss.Sizes.STWardII]" (the hub adds the import at merge; DECISIONS §20 blind spot)

$ name clash: grep for the public names and the wardII_ prefix on main and in the worktree
main matches above (none = clash-free)
RBM3D/Induction/WardII.lean

$ target statements (sed from the file)
143:theorem stWardII_identity (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
theorem stWardII_identity (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian)
    {σ : Fin 2 → Bool} (hσ : σ 0 ≠ σ 1) (a : Fin 2 → Zd d (sz.L n)) :
    STLKM sz n E u H σ a - zeroModeSet d (sz.L n) {0} (fun a' => STLKM sz n E u H σ a') a =
      (((STLKM sz n E u H (fun _ : Fin 1 => true) (fun _ => a 1)).im : ℝ) : ℂ) /
        ((((sz.size n : ℕ) : ℂ)) * (etaT E u : ℂ)) := by
269:theorem stWardII_holds (d : ℕ) : STWardII d := by
theorem stWardII_holds (d : ℕ) : STWardII d := by

$ compiled nonempty instances (same file, sed)
private def wardII_szI : Sizes 3 where
  L := fun _ => 3
  W := fun _ => 1
  lam := fun _ => 1
  three_le_L := fun _ => le_rfl
  W_pos := fun _ => Nat.one_pos

/-- The identity `stWardII_identity` at `d = 3`, `L = 3`, `W = 1`, `E = 0`, `u = 1/2`, the Hermitian `H = 1` of the
`27 × 27` matrices, `σ = (+,-)`, `a = (0, e₁)`: every hypothesis (`|E| < 2`, `0 ≤ u < 1`, `H` Hermitian, `σ₁ ≠ σ₂`) is
discharged. -/
example :
    STLKM wardII_szI 0 (0 : ℝ) (1 / 2 : ℝ) (1 : Matrix (Idx 3 3 1) (Idx 3 3 1) ℂ) ![true, false]
        ![(0 : Zd 3 3), ![1, 0, 0]] -
      zeroModeSet 3 3 {0} (fun a' => STLKM wardII_szI 0 (0 : ℝ) (1 / 2 : ℝ) (1 : Matrix (Idx 3 3 1) (Idx 3 3 1) ℂ)
        ![true, false] a') ![(0 : Zd 3 3), ![1, 0, 0]] =
      (((STLKM wardII_szI 0 (0 : ℝ) (1 / 2 : ℝ) (1 : Matrix (Idx 3 3 1) (Idx 3 3 1) ℂ)
          (fun _ : Fin 1 => true) (fun _ => (![1, 0, 0] : Zd 3 3))).im : ℝ) : ℂ) /
        ((((wardII_szI.size 0 : ℕ) : ℂ)) * (etaT (0 : ℝ) (1 / 2 : ℝ) : ℂ)) :=
  stWardII_identity wardII_szI 0 (by norm_num) (by norm_num) (by norm_num) Matrix.isHermitian_one
    (by decide) _

end RBM.Gauss.Sizes

namespace RBM.Gauss.Step5Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst RBM.Path Filter

/-- `stWardII_holds 3` applied at the Step-5 instance data `(szB, zB, 15/16, 31/32)` (regime (ii): `1-t = 1/32 ≥ ilambda²/L^3 = 1/64`,
`1-s = 1/16 = ilambda²/L²`); the stochastic premises `STKbound ... STLKU` stay hypotheses (other gates' pins). -/
example (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STWardIIConcl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) Cd :=
  inst_wardII (stWardII_holds 3) Cd hCd

end RBM.Gauss.Step5Inst
```

Narrative (all facts are in the script output above):
- New file `RBM3D/Induction/WardII.lean` (364 lines, imports `Induction.Step5Cases`, `Induction.ConArgDet`, `Loop.KLWard`; not `RBM3D`); `RBM3D/Test/Axioms.lean` only loses the owed-registry line of `RBM.Gauss.Sizes.STWardII` (1 deletion).
- Target 1 `stWardII_identity` (deterministic: Hermitian `H`, `|E| < 2`, `0 ≤ u < 1`, `σ₁ ≠ σ₂`). Sign is `+` for both orders, as section (a) row 4 found: `X - Q^{(1)}X = +Im X^{(1)}_{+,a₂}/(Nη_u)`.
  - `𝓛` side: private `wardII_sum` is `(WI_calL)` summed over the FIRST label, from the merged `sum_gloop_two_ward` (second-label sum): trace-cyclic rotation `wardII_loopL_rot` for `σ = (-,+)`, and the conjugate spectral parameter (`wardII_loopL_conj`, `Gres H z̄ true = Gres H z false`) for `σ = (+,-)`.
  - `𝒦` side: `KLK_rotate` then `KLward_two` (the `n = 2` form of `KLK_ward`, `Loop/KLTree.lean:457`), `KLK_one`.
  - `𝓛^{(1)}_- = conj 𝓛^{(1)}_+` for Hermitian `H` (`wardII_one_conj`) and `m(-) = conj m(+)` turn the difference into `2i Im`; `N = (WL)^d = W^d L^d`.
- Target 2 `stWardII_holds d : STWardII d`: `hS2.2.1 = STAvgU` (inside `STStep2Concl`, section (a) (iii)) is pulled back to the index `(u,σ,a)` by `StochDomAt.precomp_param` at `(u, +, a₂)`; the identity gives `ξ ≤ (Nη_u)⁻¹ · |𝓛^{(1)}-𝒦^{(1)}|` (`wardII_prec_scale`); `wardII_Bctl_le` gives `W^{-d}B_{u,0} ≤ 2A⁻¹` from `1-u ≥ 1-t ≥ ilambda²/L^d` only (the window `1-s ≤ ilambda²/L²` is not used); the factor 2 goes through `st5_prec_mono`.
- Used merged hypotheses of `STIngR5`: `STFlow` (for `|E_n| < 2`, `t < 1`, `∀ᶠ 0 < ilambda`), `s ≥ 0`, `t ≤ lemT`, `STStep2Concl` (only its `STAvgU` part); the other premises are unused.
- Instances: (1) identity at `d = 3`, `L = 3`, `W = 1`, `E = 0`, `u = 1/2`, `H = 1` (Hermitian `27 × 27`), `σ = (+,-)`, `a = (0, e₁)`, all hypotheses discharged by `norm_num`, `Matrix.isHermitian_one`, `decide`; (2) `inst_wardII (stWardII_holds 3) Cd hCd` at the merged Step-5 data `(szB, zB, 15/16, 31/32)`, with the stochastic premises of `InstIng5Concl` left as that definition's own hypotheses (other gates' pins).
- No port from RBM1D/RBM2D: nothing was read or copied from them, so no `diff --stat` is owed. The private proofs `wardII_*` were written against the merged `cad_*` patterns of `Induction/ConArgDet.lean` (private there, so re-proved here).
- Full `lake build` needs the root import (hub, at merge); I checked it with the import line added temporarily in my worktree and restored `RBM3D.lean` (see (b)).

## (c) Verified Mathlib names used (all compile in `WardII.lean`)
- `Matrix.trace_mul_comm`, `Matrix.trace_conjTranspose`, `Matrix.diagonal_conjTranspose`, `Matrix.conjTranspose_nonsing_inv`, `Matrix.isHermitian_one`, `Matrix.IsHermitian.submatrix` (via `hH.submatrix _`).
- `Finset.toList_singleton`, `Complex.sub_conj`, `Complex.abs_im_le_norm`, `Complex.conj_conj`, `Complex.conj_im`, `inv_anti₀`, `lt_of_mul_lt_mul_left`, `div_le_iff₀`.
- Merged project names used: `RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero`, `RBM.Ind.Gres_eq_green_zSig`, `RBM.sum_gloop_two_ward`, `RBM.Loop.KLward_two`, `RBM.Loop.KLK_rotate`, `RBM.Loop.KLK_one`, `StochDomAt.precomp_param`, `st5_prec_mono`, `st5_t_lt_one`, `st5_eventually_A_ge_one`, `st5_STAI_nonneg`, `etaT_pos`, `etaT_eq_zt_im`, `lemma28_quant`, `Sizes.seqHflow_isHermitian`, `inst_wardII`.
- Names verified absent: none searched for.

## (d) Open issues and paper-delta candidates
- No open issue; no change to a frozen or pinned signature; the pin `STWardII` is true as stated (section (a) verdict confirmed by the proof).
- T2148a: the identity `(zYU1)` has the sign `+` for both `σ ∈ {(+,-),(-,+)}` (the ticket's "±" resolves to `+`), and needs `H` Hermitian, `|E| < 2`, `0 ≤ u < 1` as deterministic side conditions of the Lean statement.
- T2148b: `Δ_u ≍ A⁻¹` of `3_5:2259` is used as `W^{-d}B_{u,0} ≤ 2A⁻¹` (constant 2, from `1-u ≥ ilambda²/L^d`), absorbed by `N^τ` in `≺`; only the upper bound is needed.
- Registry: `RBM.Gauss.Sizes.STWardII` deleted from the owed list of `RBM3D/Test/Axioms.lean`; with it deleted, the pre-check (import `RBM3D` plus the new module) exits 0.
