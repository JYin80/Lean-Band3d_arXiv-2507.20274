Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct 10 03:26:51 UTC 2026

Scripts (Python, no Lean): `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/966b45d4-be15-4db2-88b3-45a074bfecd5/scratchpad/T2369/{n2.py,inst.py,kode.py}`; `kode.py` is the copy of T2360's `S/kode.py` (ODE `treeEqRhsS`, `S = I`, RK4, BA data from `(self_m)`). BA loop = `W^{-(n-1)d} ∏_i M(σ_i)[a_{i-1}, a_i]`, evaluated by the K00 form (`zip σ (zip (rotate a (n-1)) a)`, `BA/FlowPins.lean:274`, merged `BAMLoop`; `BAMLoop_apply`, `BA/KBase.lean:54`).

### (i) Exponent table, and the use-by-use map

No exponent enters (`3 ≤ d` is not used; `d` is free). The constants:

| Quantity | Value / form | Constraint | Slack |
|---|---|---|---|
| `η_t` | `(1-t)·Im m(+)` (pin: `(((1-t)*(m true).im : ℝ) : ℂ)`) | `≠ 0` for `κ_t = (2i W^d η_t)⁻¹` and `∂_tκ_t = κ_t/(1-t)` | `1-t > 0` on `[0,1)`, `Im m(+) > 0` (hypothesis); instance `Im m = 0.807159`, `1-t ∈ {0.5, 0.1}` |
| `κ_t (m(+) - m(-))` | `(W^d (1-t))⁻¹` | from `m(-) = conj m(+)` alone: `m - conj m = 2i Im m` | exact; no `‖m‖ = 1` (band `KLWard_mSigma_mul`, `KLWard.lean:606`, used only at `:710`, i.e. only in the `t = 0` step, which is now a hypothesis) |
| `W` | `1 ≤ W` | `(W:ℂ) ≠ 0` | `W = 1` in the instance (`W^d = 1`), generic `W ≥ 1` |
| `L` | generic: none; band `kernelFacts_SB`: `3 ≤ L`; BA: none needed | `sum_SB_row` needs `3 ≤ L` | `L = 5` |
| time horizon `T₀` | any `T₀ < 1` (pin: `t ∈ [0,1)`) | `RetireS` (`Loop/Unique.lean:106`) gives `R ≥ 0` with `‖K t I‖ ≤ R` on `[0,T₀]`, `I.length = 2` | Grönwall constant in `KLWard_level` (`:749`) is a finite sum over `Zd d L` with `W^d` and `R` (`KLWard.lean:52-54`) |
| kernel | `‖S a b‖ ≤ 1` (Grönwall), `S` symmetric (cyclic invariance; `KLWard.lean:504`), `conj S = S` (flip; `:996`), `∑_a S a b = 1` (`:363-365`) | the four `KernelFacts` fields | `S = 1`: `0.0, 0.0, 0.0, max entry 1.0` (`inst.out`) |
| stop line | `≤ 1000` net lines | `(KLWard − 1224) + wc -l BA/KWard` | estimate 450–650 (see (iv)): slack ≥ 350 |
| N2 stop | defect at `t = 0` `≤ 1e-6` | hypothesis as pinned true for BA | max `3.3e-16`: slack factor `3e9` |

**Use-by-use map** (line numbers: merged `RBM3D/Loop/KLWard.lean`):

| Use | Where | Replaced by |
|---|---|---|
| `SB d L g` | §2 `:219-572` (statements of `sum_treeEqRhs_fullLoop`, `cut_inner`, `cut_last`, `cut_one_last`, `rhs_identity`), §4 `:739-866` | `S`; `treeEqRhs` becomes `treeEqRhsS` (`KLTree.lean:809`, same summand `K(cutL)·S a b·K(cutR)`); `:363-365` column sum `= KernelFacts.colSum`; `:504` transposition `= .symm`; `KLWard_norm_SB_apply_le` (`:739`) `= .entry` |
| `SB` | §5 `KLWard_conj_SB` (`:996`, used `:1008`) | `.real` |
| `MLoop` | `KLWard_wD_MLoop` (`:685`) | pin hypothesis at `t = 0` (`|μ| ≥ 1`), band instance kept; `:923`: `hK.2.1` gives `K 0 I = M I`; `KLWard_conj_MLoop_flip` (`:1018`) gives the flip hypothesis; rotation: `KLUnique_MLoop_rot_cons` (`KLUnique.lean:637`) is `private` there, so a private reproof (`List.map_rotate`, `List.rotate_perm`, as `KLUnique.lean:467-473`) is added in `KLWard.lean` |
| `mSigma` | `kappa_mul` (`:612`), `wD_MLoop`, `conj_mSigma_not` (`:1013`), `isKLoop_flip` | `m` with `m false = conj (m true)` and `0 < (m true).im`; `kappa_mul` uses `Complex.sub_conj` only |
| `KLK` | `isKLoop_flip` (`:1032`), `KLWard_flip` (`:1051`), `KLWard_pos` (`:1071`), `KLK_ward` (`:1123`) | an arbitrary `K` with `IsKLoopS`; `KLK` only in the G1 instance |
| `KLK_isKLoop` | `:1035`, `:1078` | hypothesis `IsKLoopS … K` of the pin; G1: `KLK_isKLoop` + `IsKLoop_iff_IsKLoopS` (`KLTree.lean:846`, `Iff.rfl`) |
| `KLK_rotate` | `:1090` | `rotS_holds` (`KLUnique.lean:693`): needs `S` symmetric, `‖S‖ ≤ 1`, rotation hypothesis on `M` |
| `KLK_unique` | `:1056` | `uniqS_holds` (`Unique.lean:291`) at `K' = conj∘K∘flip` (`IsKLoopS` by `.real`, `m(-) = conj m(+)`, flip hypothesis; `treeEqRhs_flip` `:1002`); gives length `≥ 2`; length `1` is clause 3 |
| `KLretire_twoLoopBounded` | `:1080` | `retireS_holds` (`Unique.lean:347`) |
| `KLward_two` | `:1098` | level-2 hypothesis of the pin plus clause 3 (`K ⟨[s],[a]⟩ = m s`) and `kappa_mul`: `wD [] [a] = c − κ(m − m̄) = 0` |
| `KLWard_mSigma_mul` | `:710` only | dropped from the generic part (not a hypothesis); band instance only |
| `Gauss.etaT` | `:598, 604, 634-646, 1108, 1126-1162` | `(((1-t)*y : ℝ) : ℂ)`, `y = (m true).im`; `∂_t` uses `y ≠ 0`; band: `etaT E t = (1-t)*(mE E).im` is `rfl` (`:604`), `(mSigma E true).im = (mE E).im` |

### (ii) Paper computations (K00 indexing: `σ_i` on the edge `(a_{i-1}, a_i)`, cyclic; `paper/tex/1_2_Intro_model_result.tex:1003`, `(WI_calK)` `:1034-1046`)

**`t = 0` identity.** Take `I = ⟨+::μ++[-], a++[x]⟩`, `a = (a_0..a_{N-1})`, `N = |μ|+1 ≥ 2`. Only two factors carry `x`: `σ_0 = +` on `(x, a_0)` (cyclic predecessor of `a_0` is `x`) and the last charge `-` on `(a_{N-1}, x)`. So
`∑_x 𝓜 = W^{-Nd} P · ∑_x M(-)_{a_{N-1} x} M(+)_{x a_0} = W^{-Nd} P · (M^* M)_{a_{N-1} a_0}`, `P = ∏_{i=1}^{N-1} M(μ_{i-1})_{a_{i-1} a_i}`, using `M(-) = M^*`.
The right side loops `⟨±::μ, a⟩` carry `M(±)_{a_{N-1} a_0}` with the same `P`, and `W^{-(N-1)d}`; their difference is `W^{-(N-1)d} P (M - M^*)_{a_{N-1} a_0}`. The hypothesis `= (2i W^d Im m)⁻¹ (…)` is therefore equivalent to the entrywise identity `M - M^* = 2i Im m · M^* M` (with `Im z = 0`).
**How `BAMB_ward_row` enters: it does not close it.** `BAMB_ward_row` (`BA/Ward.lean:108`) states `(Im m + Im z) ∑_b ‖M_ab‖² = Im m` (the diagonal entry `a = a_0 = a_{N-1}` of the identity, under `BASelf`); the entrywise identity is the resolvent identity: with `H = gΨ` Hermitian, `w = E + m`, `Im w = Im m > 0`, `G = (H - w)⁻¹ = M`, `G^* = (H - w̄)⁻¹`: `G^* (H - w) G - G^* (H - w̄) G = G^* - G = (w̄ - w) G^* G`, i.e. `G - G^* = 2i Im m G^*G`. It needs only the two invertibilities (`RBM.isUnit_sub_smul_of_isHermitian`, `Analysis/Resolvent.lean:132`, already used at `BA/MFixedPoint.lean:730`) and `Im m > 0` from `BAReal`; a new private lemma of ≈ 45 lines in `BA/KWard.lean`. No hypothesis beyond the targets'.
**Flip:** `M(¬σ)_{xy} = conj M(σ)_{xy}` (`M(-) = M^*`, `BAMB_symm`, `BA/Ward.lean:83`); `W^d` real; so `BAMLoop(flip I) = conj BAMLoop(I)` factor by factor.
**Rotation:** `⟨s::σ, b::a⟩` and `⟨σ++[s], a++[b]⟩` carry the same multiset of edge factors (`s` on `(a_last, b)`, `σ_i` on `(a_{i-1}, a_i)`), the product commutes. `PropSpin m false = conj m` by definition.
**Level 2 from `(Kn2sol)`:** `K t ⟨[σ₁,σ₂],[a₁,a₂]⟩ = W^{-d} (Θ^{(σ₁σ₂)} M^{(σ₁σ₂)})_{a₁a₂}`. For `(+,-)`: `∑_x (Θ M)_{a x} = ∑_y Θ_{ay} ∑_x M^{(+-)}_{yx} = ∑_y Θ_{ay} = (1-t)⁻¹`, with `M^{(+-)} = BAK` (`BAMss_pm_eq`, `BATheta_pm_eq`, `BA/KKernel.lean:107`), `∑_x BAK_{yx} = 1` (`BAK_row_sum`, `BA/KKernel.lean:124`) and `BATheta_row_sum_pm` (`BA/KBase.lean:381`, `0 ≤ t < 1`). So `∑_x K = (W^d (1-t))⁻¹`, the pin's level-2 hypothesis.

**Instance** (`d = 1`, `L = 5`, `W = 1`, `g = 0.5`, `E = 0.3`, `κ = 0.5`; no external hypothesis occurs, so no limit computation; the family `K` is the RK4 solution of `treeEqRhsS` with `S = 1`, `M = BAMLoop`, existence on `[0,1)` is not proved here (`BAKsolve`, T2368)):
```
$ cd /; python3 <scratchpad>/T2369/inst.py        # S = scratchpad/T2369
d=1 L=5 W=1 g=0.5 E=0.3 kappa=0.5: m=-0.068889+0.807159j  Im m=0.807159 >0: True  kappa<=Im m: True  |(self_m) residual|=2.8e-16  3<=L: True  1<=W: True
KernelFacts(S=1): symm 0.0  real 0.0  colSum-1 0.0  max entry norm 1.0
Im m>0 and m(-)=conj m(+): PropSpin by definition; Mm(-)=M^H, M symmetric: 1.2412670766236366e-16
t=0 hyp, lengths 3,4,5: {3: '2.2e-16', 4: '2.2e-16', 5: '1.1e-16'}  flip(n=2..5)=1.1e-16 rot(n=2..5)=5.7e-17
t=0.5: level-2 sum defect=1.9e-13; (WI_calK) defect by length n=2,3,4: {2: '1.9e-13', 3: '2.0e-13', 4: '4.4e-12'}
t=0.9: level-2 sum defect=3.6e-12; (WI_calK) defect by length n=2,3,4: {2: '3.6e-12', 3: '1.9e-11', 4: '9.0e-10'}
```
Entrywise identity (4 data sets, `E = 0.3`): `max|M - M^H - 2i Im m M^H M| ≤ 6.7e-16` and the same with `M M^H` (`≤ 6.7e-16`).

### N2 table (B8: `d = 1`, `W = 1`, `q ∈ {4,5}`, `E = 0.3`, `g ∈ {0.2, 0.5}`; `python3 <scratchpad>/T2369/n2.py`; targets `≤ 1e-8`; stop line `1e-6` at `t = 0`)
```
t=0 hypothesis of WardS on BAMLoop: max |lhs-rhs| over all (mu,a); lengths 3,4,5 = |mu|+2; flip, rotation defects (n=2..5)
q=4 g=0.2 Im m=0.9523 {3: 2.2e-16, 4: 2.3e-16, 5: 3.3e-16} flip=2.3e-17 rot=1.3e-16
q=4 g=0.5 Im m=0.8281 {3: 2.2e-16, 4: 2.3e-16, 5: 2.3e-16} flip=4.2e-17 rot=1.1e-16
q=5 g=0.2 Im m=0.9512 {3: 2.2e-16, 4: 2.3e-16, 5: 2.3e-16} flip=2.1e-17 rot=2.2e-16
q=5 g=0.5 Im m=0.8072 {3: 2.2e-16, 4: 2.2e-16, 5: 1.1e-16} flip=1.1e-16 rot=5.7e-17
(WI_calK) for the ODE solution, lengths n = 2,3,4 (RK4: 600 steps at t=0.5, 4000 at t=0.9; level-2 sum defect = n=2 entry)
q=4 g=0.2 t=0.5 {2: 1.9e-13, 3: 1.8e-13, 4: 1.7e-11}   q=4 g=0.2 t=0.9 {2: 3.7e-12, 3: 2.8e-11, 4: 2.2e-09}
q=4 g=0.5 t=0.5 {2: 1.9e-13, 3: 1.9e-13, 4: 5.7e-12}   q=4 g=0.5 t=0.9 {2: 3.7e-12, 3: 2.2e-11, 4: 1.3e-09}
q=5 g=0.2 t=0.5 {2: 1.9e-13, 3: 1.8e-13, 4: 1.7e-11}   q=5 g=0.2 t=0.9 {2: 3.5e-12, 3: 2.7e-11, 4: 2.1e-09}
q=5 g=0.5 t=0.5 {2: 1.9e-13, 3: 2.0e-13, 4: 4.4e-12}   q=5 g=0.5 t=0.9 {2: 3.6e-12, 3: 1.9e-11, 4: 9.0e-10}
```
Max defect at `t = 0`: `3.3e-16`; max `(WI_calK)`: `2.2e-9` at `t = 0.9`, `n = 4` (RK4 truncation: with 600 steps the same entry was `4.3e-6`, with 4000 steps `2.2e-9`). All `≤ 1e-8`.

### (iv) Plan against the stop line 1000 (net growth of `KLWard.lean` over 1224 plus `wc -l BA/KWard.lean`)
1. `KLWard.lean`: pins `KernelFacts`, `WardS` copied (≈ 35); §1 unchanged (index bookkeeping, no `S`); §2–§4 generic: `SB d L g ↦ S`, `treeEqRhs ↦ treeEqRhsS`, `hL`/`|E|<2` hypotheses replaced by the four facts and `0 < y` (≈ 250 edited lines, net ≈ −20); generic `κ_t` with `y = Im m` (≈ 0 net); §5 generic flip by `uniqS_holds` + `retireS_holds` (≈ 0 net); §6 generic `pos`/flip assembly into `wardS_holds` (≈ 0 net); G1: `kernelFacts_one`, `kernelFacts_SB` (≈ 20), private `MLoop` rotation (≈ 15), band hypotheses of `WardS` at `(SB, mSigma E, MLoop)` (`t = 0` from `KLWard_wD_MLoop` `sub_eq_zero`, flip, level 2: ≈ 50), `KLK_ward` and `KLWard_flip` as thin wrappers, the old band proofs deleted (≈ −60). Net growth ≈ +100 … +200.
2. `BA/KWard.lean` (new): flip of `BAMLoop` (≈ 25), rotation `BAKWard_BAMLoop_rot` private (≈ 45), cons-split of `BAMLoop` isolating the two `x`-factors (≈ 35), resolvent identity `M - M^* = 2i Im m M^*M` (≈ 45), `t = 0` identity (≈ 60), level 2 (≈ 25), `baK_ward` assembly (≈ 30), instance and header (≈ 60): ≈ 325 … 450.
3. Total ≈ 450 … 650, below 1000 with slack ≥ 350. `BAKward` and `BAKsolve` are not pinned here.

### Verdicts
- Target 1 (pins `KernelFacts`, `WardS`): **PASS**. `WardS` is satisfiable: the `t = 0` hypothesis, flip, rotation and level 2 hold at the instance (max `3.3e-16`); no hypothesis beyond the pin.
- Target 2 (`wardS_holds`): **PASS**. The paper argument (ODE defect, Grönwall, flip by uniqueness) uses `S` only through the four fields; `‖m‖ = 1` is not needed (`κ_t(m - m̄) = c_t` from `m(-) = conj m(+)`).
- Target 3 (G1, `kernelFacts_one`, `kernelFacts_SB`, `KLK_ward`, `KLWard_flip`): **PASS**. Not a pin repair: `KLUnique_MLoop_rot`/`_cons` are `private` in `KLUnique.lean`, so the rotation of `MLoop` is reproved privately inside `KLWard.lean`.
- Target 4 (`baK_ward`): **PASS**. No hypothesis beyond `BAReal`, `1 ≤ W`, `IsKLoopS`, `(Kn2sol)`. `BAMB_ward_row` gives only the diagonal; the entrywise `M - M^* = 2i Im m M^*M` is a new private resolvent lemma (no new hypothesis).

## (b) Script output (Sat Oct 10 05:33:40 UTC 2026)

### b1. Builds and checks (worktree `RBM3D-wt/T2369`, branch `t/T2369`; `RBM3D.lean` does not import `BA/KWard`, the hub adds it at merge)
```
$ lake build RBM3D.Loop.KLWard RBM3D.BA.KWard 2>&1 | tail -1;  lake build 2>&1 | tail -1
Build completed successfully (3740 jobs).
Build completed successfully (4177 jobs).
$ lake env lean docs/tickets/checks/T2369-check.lean >/dev/null 2>&1; echo exit $?   # Part 2: KLK_ward, KLWard_flip statements unchanged
exit 0
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Loop/KLWard.lean RBM3D/BA/KWard.lean; echo "grep exit $?"
grep exit 1
$ git show a5c1a1a:RBM3D/Loop/KLWard.lean | wc -l; wc -l RBM3D/Loop/KLWard.lean RBM3D/BA/KWard.lean; git diff --stat main...t/T2369   # stop line 1000
    1224
    1424 RBM3D/Loop/KLWard.lean
     399 RBM3D/BA/KWard.lean
    1823 total
 RBM3D/BA/KWard.lean    | 399 ++++++++++++++++++++++++++
 RBM3D/Loop/KLWard.lean | 754 +++++++++++++++++++++++++++++++------------------
 2 files changed, 876 insertions(+), 277 deletions(-)
net = (1424 - 1224) + 399 = 599 <= 1000
```

### b2. Axioms (`lake env lean axioms.lean`: `import RBM3D.Loop.KLWard RBM3D.BA.KWard`, `#print axioms` of the 16 names below)
```
16 names printed; distinct axiom sets: ['[propext, Classical.choice, Quot.sound]']; names without "depends on axioms": 0
Loop.WardS, Loop.wardS_holds, Loop.kernelFacts_one, Loop.kernelFacts_SB, Loop.KLK_ward, Loop.KLWard_flip, Loop.KLWardInst_kernelFacts_one, Loop.KLWardInst_kernelFacts_SB, Loop.KLWardInst_wardS, Loop.KLWardInst_ward_true, Loop.KLWardInst_ward_false, Loop.KLWardInst_ward_two_false, Loop.KLWardInst_ward_four_false, Loop.KLWardInst_flip, BA.baK_ward, Loop.KernelFacts
(KernelFacts: structure, WardS: def; both print the standard set too)
```

### b3. Pins against the check file (29-line blocks `KernelFacts` + `WardS` cut from both files by script)
```
$ diff pins_check.txt pins_branch.txt; echo "diff exit $?"; wc -l < pins_check.txt; wc -l < pins_branch.txt
diff exit 0
      29
      29
$ lake env lean pin1.lean (KernelFacts <-> check copy, field by field); lake env lean rfl_check.lean (WardS = check-file text, `rfl`); echo $?
pin1 exit 0
rfl_check exit 0
```
(In `rfl_check.lean` the `def WardS` text of the check file is placed in a namespace where `KernelFacts` resolves to the branch structure, then `example : RBM.Loop.WardS = RBM.Loop.T2369Copy.WardS := rfl`.)

### b4. Target statements, extracted from the files by script
```
Loop/KLWard.lean:93-97
structure KernelFacts {d L : ℕ} [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℂ) : Prop where
  symm : ∀ a b, S a b = S b a
  real : ∀ a b, (starRingEnd ℂ) (S a b) = S a b
  colSum : ∀ b, ∑ a, S a b = 1
  entry : ∀ a b, ‖S a b‖ ≤ 1
Loop/KLWard.lean:103-119  def WardS (pin, 25 lines, identical to the check file by b3)
Loop/KLWard.lean:1175
theorem wardS_holds : WardS := by
Loop/KLWard.lean:1215
theorem kernelFacts_one {d L : ℕ} [NeZero L] : KernelFacts (1 : Matrix (Zd d L) (Zd d L) ℂ) where
Loop/KLWard.lean:1222
theorem kernelFacts_SB {d L : ℕ} [NeZero L] (g : ℝ) (hL : 3 ≤ L) : KernelFacts (SB d L g) where
BA/KWard.lean:305  (section variables: variable (d L W : ℕ) [NeZero L], BA/KWard.lean:51)
theorem baK_ward (g κ E : ℝ) (m : ℂ) (hr : BAReal d L g κ E m) (hL : 3 ≤ L) (hW : 1 ≤ W)
    {K : ℝ → LoopIdx (Zd d L) → ℂ}
    (hK : IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) (PropSpin m)
      (BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m))) (Set.Ico (0 : ℝ) 1) K)
    (hn2 : ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (σ : Bool × Bool) (a₁ a₂ : Zd d L),
      K t ⟨[σ.1, σ.2], [a₁, a₂]⟩ = (((W : ℂ) ^ d)⁻¹) *
        (BATheta d L g E m t σ.1 σ.2 * BAMss d L (BAMB d L g (E : ℂ) m) σ.1 σ.2) a₁ a₂) :
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (s : Bool) (μ : List Bool) (a : List (Zd d L)), a.length = μ.length + 1 →
      ∑ x : Zd d L, K t ⟨s :: μ ++ [!s], a ++ [x]⟩
        = (2 * Complex.I * (W : ℂ) ^ d * (((1 - t) * (PropSpin m true).im : ℝ) : ℂ))⁻¹ *
            (K t ⟨true :: μ, a⟩ - K t ⟨false :: μ, a⟩) := by
KLK_ward: statement text on main == branch: True  (`@KLK_ward` also elaborates against the check file, b1)
KLWard_flip: statement text on main == branch: True  (`@KLWard_flip` also elaborates against the check file, b1)
```

### b5. Compiled nonempty instances (all compile in the builds of b1)
```
Loop/KLWard.lean:1399
theorem KLWardInst_kernelFacts_one : KernelFacts (1 : Matrix (Zd 3 5) (Zd 3 5) ℂ) := kernelFacts_one
Loop/KLWard.lean:1402
theorem KLWardInst_kernelFacts_SB : KernelFacts (SB 3 5 (1 / 2)) := kernelFacts_SB (1 / 2) (by norm_num)
Loop/KLWard.lean:1408-1420  wardS_holds at d=3, L=5, W=2, S=SB 3 5 (1/2), m=mSigma 0, M=MLoop, K=KLK, t=9/10, loop (+,-,-); every hypothesis discharged in the proof term (lines 1414-1420)
theorem KLWardInst_wardS :
    ∑ x : Zd 3 5, KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨true :: [false] ++ [!true], [0, 1] ++ [x]⟩
      = (2 * Complex.I * (2 : ℂ) ^ 3 * (((1 - 9 / 10) * (mSigma 0 true).im : ℝ) : ℂ))⁻¹ *
          (KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨true :: [false], [0, 1]⟩
            - KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨false :: [false], [0, 1]⟩) 
unchanged, recompiled: KLWardInst_ward_true, _ward_false, _ward_two_false, _ward_four_false, _flip
BA/KWard.lean:385-395  baK_ward at the flow point P of (d,L)=(3,4), W=2, t=1/2 (BAReal := P.real discharged; K, IsKLoopS, (Kn2sol) = BAKsolve of T2368 stay hypotheses, see b9)
example (K : ℝ → LoopIdx (Zd 3 4) → ℂ)
    (hK : IsKLoopS 3 4 2 (1 : Matrix (Zd 3 4) (Zd 3 4) ℂ) (PropSpin P.m0)
      (BAMLoop 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0))) (Set.Ico (0 : ℝ) 1) K)
    (hn2 : ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (σ : Bool × Bool) (a₁ a₂ : Zd 3 4),
      K t ⟨[σ.1, σ.2], [a₁, a₂]⟩ = (((2 : ℂ) ^ 3)⁻¹) *
        (BATheta 3 4 P.g0 P.E P.m0 t σ.1 σ.2 * BAMss 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) σ.1 σ.2) a₁ a₂) :
    ∑ x : Zd 3 4, K (1 / 2) ⟨true :: [false] ++ [!true], [0, ![1, 0, 0]] ++ [x]⟩
      = (2 * Complex.I * (2 : ℂ) ^ 3 * (((1 - 1 / 2) * (PropSpin P.m0 true).im : ℝ) : ℂ))⁻¹ *
          (K (1 / 2) ⟨true :: [false], [0, ![1, 0, 0]]⟩ - K (1 / 2) ⟨false :: [false], [0, ![1, 0, 0]]⟩) :=
  baK_ward 3 4 2 P.g0 P.m0.im P.E P.m0 P.real (by norm_num) (by norm_num) hK hn2 (1 / 2)
    ⟨by norm_num, by norm_num⟩ true [false] [0, ![1, 0, 0]] rfl
BA/KWard.lean:367-379  level-2 consequence of baK_ward, EVERY hypothesis discharged (explicit family, (Kn2sol) by rfl; all t in [0,1), all a)
private def BAKWardInst_K2 : ℝ → LoopIdx (Zd 3 4) → ℂ := fun t I =>
  match I.σ, I.a with
  | [s₁, s₂], [a₁, a₂] => (((2 : ℂ) ^ 3)⁻¹) *
      (BATheta 3 4 P.g0 P.E P.m0 t s₁ s₂ * BAMss 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) s₁ s₂) a₁ a₂
  | _, _ => 0

...
example : ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ a : Zd 3 4,
    ∑ x : Zd 3 4, BAKWardInst_K2 t ⟨[true, false], [a, x]⟩ = (((2 : ℂ) ^ 3) * ((1 - t : ℝ) : ℂ))⁻¹ :=
  BAKWard_two 3 4 2 P.g0 P.m0.im P.E P.m0 P.real (K := BAKWardInst_K2) (fun t ht σ a₁ a₂ => rfl)
also unconditional at P (BA/KWard.lean examples at lines 341, 352, 360): t=0 identity BAKWard_zero at length 4 with the sum over x; flip; rotation of BAMLoop
```

### b6. Name clashes, public-name diff, port provenance
```
$ git grep -nE "^(private )?(theorem|def|structure|lemma|abbrev) (KernelFacts|WardS|wardS_holds|kernelFacts_one|kernelFacts_SB|baK_ward|KLWardInst_wardS|KLWardInst_kernelFacts_one|KLWardInst_kernelFacts_SB)( |$)" main -- RBM3D | wc -l   [main, and t/T2363 t/T2364 t/T2365 t/T2367 t/T2368]
main=0
 t/T2363=0
 t/T2364=0
 t/T2365=0
 t/T2367=0
 t/T2368=0
 
main:RBM3D/Loop/KLUnique.lean:864:(`S^{(B)}(0) = I`, `kernelFacts_one` of the probe `t/T2360`): symmetry, `‖S a b‖ ≤ 1`,
$ public names of Loop/KLWard.lean, a5c1a1a vs branch (comm)
deleted/renamed: (none)
added: KernelFacts, kernelFacts_one, kernelFacts_SB, KLWardInst_kernelFacts_one, KLWardInst_kernelFacts_SB, KLWardInst_wardS, WardS, wardS_holds
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h; git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Loop/Ward.lean; grep -c RBM2D RBM3D/BA/KWard.lean
9e0f275
 RBM2D/Loop/Ward.lean | 61 +++++++++++++++++++---------------------------------
 1 file changed, 22 insertions(+), 39 deletions(-)
0
```
`Loop/KLWard.lean` is the T2036 port of `RBM2D/Loop/Ward.lean` at `c9a24cf` (pre-existing header); this ticket edits it in place; `BA/KWard.lean` has no port (grep count 0).

### b7. N2 table re-run (`python3 n2.py`, same script as (a); B8: d=1, W=1, q in {4,5}, E=0.3, g in {0.2,0.5}; target <= 1e-8, stop line 1e-6 at t=0)
```
t=0 hypothesis (max |lhs-rhs| over mu,a), flip, rotation defects of BAMLoop
q=4 g=0.2 E=0.3 Im m=0.9523 |m|=0.9624 {3: '2.2e-16', 4: '2.3e-16', 5: '3.3e-16'} flip=2.3e-17 rot=1.3e-16
q=4 g=0.5 E=0.3 Im m=0.8281 |m|=0.8364 {3: '2.2e-16', 4: '2.3e-16', 5: '2.3e-16'} flip=4.2e-17 rot=1.1e-16
q=5 g=0.2 E=0.3 Im m=0.9512 |m|=0.9612 {3: '2.2e-16', 4: '2.3e-16', 5: '2.3e-16'} flip=2.1e-17 rot=2.2e-16
q=5 g=0.5 E=0.3 Im m=0.8072 |m|=0.8101 {3: '2.2e-16', 4: '2.2e-16', 5: '1.1e-16'} flip=1.1e-16 rot=5.7e-17
(WI_calK) for the ODE solution, W=1, RK4 600 steps at t=0.5, 4000 at t=0.9; level-2 hypothesis defect
q=4 g=0.2 E=0.3 t=0.5 {2: '1.9e-13', 3: '1.8e-13', 4: '1.7e-11'} level2 sum-defect=1.9e-13
q=4 g=0.2 E=0.3 t=0.9 {2: '3.7e-12', 3: '2.8e-11', 4: '2.2e-09'} level2 sum-defect=3.7e-12
q=4 g=0.5 E=0.3 t=0.5 {2: '1.9e-13', 3: '1.9e-13', 4: '5.7e-12'} level2 sum-defect=1.9e-13
q=4 g=0.5 E=0.3 t=0.9 {2: '3.7e-12', 3: '2.2e-11', 4: '1.3e-09'} level2 sum-defect=3.7e-12
q=5 g=0.2 E=0.3 t=0.5 {2: '1.9e-13', 3: '1.8e-13', 4: '1.7e-11'} level2 sum-defect=1.9e-13
q=5 g=0.2 E=0.3 t=0.9 {2: '3.5e-12', 3: '2.7e-11', 4: '2.1e-09'} level2 sum-defect=3.5e-12
q=5 g=0.5 E=0.3 t=0.5 {2: '1.9e-13', 3: '2.0e-13', 4: '4.4e-12'} level2 sum-defect=1.9e-13
q=5 g=0.5 E=0.3 t=0.9 {2: '3.6e-12', 3: '1.9e-11', 4: '9.0e-10'} level2 sum-defect=3.6e-12
```
Max defect at t = 0: 3.3e-16; max (WI_calK) defect: 2.2e-9 (t = 0.9, n = 4, RK4 truncation). All <= 1e-8.

### b8. Downstream fit (scratch `compose.lean`, 60 lines, not committed): `BAKsolve d -> BAKward d` from `baK_ward` (DECISIONS §177)
```
$ lake env lean compose.lean 2>&1 | grep -E "error|axioms"; grep -n "theorem compose\|exact baK_ward\|uniqS_holds\|retireS_holds" compose.lean
'RBM.BA.compose' depends on axioms: [propext, Classical.choice, Quot.sound]
30:theorem compose (d : ℕ) (h : BAKsolveX d) : BAKwardX d := by
45:    obtain ⟨R, hR0, hR⟩ := retireS_holds d L W 1 (PropSpin m) _ hK t ht.2
46:    obtain ⟨R', hR'0, hR'⟩ := retireS_holds d L W 1 (PropSpin m) _ hsol t ht.2
47:    exact uniqS_holds d L W 1 (PropSpin m) _ kernelFacts_one.entry hK hsol (T₀ := t) (R := max R R')
57:  exact baK_ward d L W g κ E m hr hL hW hsol hn2' t ⟨ht0, ht1⟩ s μ a ha
```
(`BAKsolveX`, `BAKwardX` are the probe texts `t/T2360:RBM3D/Probe/T2360Pins.lean:281,306`; `BAKsol` is `BA/FlowPins.lean:281`.)

### b9. Narrative (each fact is visible in b1-b8 or in the files)
- `Loop/KLWard.lean` (in place): pins `KernelFacts`, `WardS` (section 0); sections 2-4 are the former band sections with `SB d L g ↦ S`,
  `treeEqRhs ↦ treeEqRhsS`; `KLWard_norm_SB_apply_le` (private) is deleted, its use is `hS.entry`; column sum and transposition are
  `hS.colSum`, `hS.symm`; `KLWard_kappa (W) (y t) = (2 i W^d (1-t) y)⁻¹`; `KLWard_kappa_mul` uses only `m(-) = conj m(+)`, `0 < Im m(+)`
  (`Complex.sub_conj`); `KLWard_mSigma_mul` (`‖m‖ = 1`) survives only inside `KLWard_wD_MLoop`, the band instance of the `t = 0` hypothesis.
- `KLWard_of_isKLoopS` (ODE defect, Grönwall, strong induction on the length) takes the pin's `t = 0` and level-2 hypotheses; cyclic invariance is
  `rotS_holds`, the 2-loop bound `retireS_holds`; the flip is `KLWard_K_flip` by `uniqS_holds` on `conj ∘ K ∘ flip` (`IsKLoopS` by `hS.real`,
  `m(-) = conj m(+)`, the flip hypothesis on `M`); `wardS_holds` assembles `s = +` and `s = -` as `KLK_ward` did.
- G1: `kernelFacts_one`, `kernelFacts_SB` (probe 211, 218); `KLK_ward`, `KLWard_flip` keep their statements and are re-derived at
  `(SB d L g, mSigma E, MLoop)` (`KLK_isKLoop` is passed as `IsKLoopS … (MLoop …)` by unfolding: `IsKLoop_iff_IsKLoopS` is `Iff.rfl`,
  `KLMLoop_eq_MLoopM` is `rfl`, `KLTree.lean:842-848`); the rotation of `MLoop` is reproved privately (`KLWard_MLoop_rot`; `KLUnique_MLoop_rot*` are
  `private` in `KLUnique.lean`). No public name deleted or renamed (b6).
- `BA/KWard.lean`: `BAKWard_BAMLoop_flip` (`M(-) = Mᴴ`, `BAMB_symm`), `BAKWard_BAMLoop_rot` (`List.zipWith_rotate_distrib`), `BAKWard_pm`/`BAKWard_full`
  (index forms by `BAMLoop_apply`: `x` sits on `M(+)_{x a_0}` and `M(-)_{a_k x}`), `BAKWard_resolvent` (`M - Mᴴ = 2 i Im m · Mᴴ M` from the two
  invertibilities, `RBM.isUnit_sub_smul_of_isHermitian`), `BAKWard_zero` (`t = 0`), `BAKWard_two` (level 2: `(Kn2sol)`, `BAMss_pm_eq`, `BAK_row_sum`,
  `BATheta_row_sum_pm`), `baK_ward`. `BAMB_ward_row` is not used: it is the diagonal entry of `M - Mᴴ = 2 i Im m · Mᴴ M` only; no hypothesis was added.
- `hL : 3 ≤ L` of `baK_ward` is unused (kept as in the ticket); `1 ≤ W` is used (`W^d ≠ 0`).
- Instance of `baK_ward`: T2368 is merged on `main` (`79dec34`, after this branch's base `a5c1a1a`). Its `baKsolveLe3_holds` gives `IsKLoopSLe … 3`
  (`RBM3D/BA/KSolve.lean:72`), not `IsKLoopS`; a family with `IsKLoopS` is `BAKsolve` (a pin, `KSolve.lean:58`), so no concrete full family exists. The
  compiled `baK_ward` example keeps `K`, `IsKLoopS`, `(Kn2sol)` as hypotheses (`BAReal`, `3 ≤ 4`, `1 ≤ 2`, `t`, the loop are discharged). Fully discharged (b5):
  the level-2 consequence with the explicit family `BAKWardInst_K2`, and the `t = 0` identity, flip and rotation of `BAMLoop`, all at the flow point `P`.

## (c) Verified Mathlib / core names used (`example := @name` each compiled, `names.lean`, exit 0)
`List.zipWith_rotate_distrib`, `List.zip_eq_zipWith`, `List.rotate_append_length_eq`, `List.rotate_rotate`, `List.rotate_length`, `List.rotate_cons_succ`,
`List.map_rotate`, `List.rotate_perm`, `List.mem_rotate`, `List.getD_append`, `List.getD_append_right`, `List.getD_cons_succ`, `List.getD_cons_zero`,
`List.zip_cons_cons`, `List.length_eq_one_iff`, `Matrix.conjTranspose_nonsing_inv`, `Matrix.nonsing_inv_mul`, `Matrix.mul_nonsing_inv`,
`Matrix.isUnit_iff_isUnit_det`, `Matrix.nonsing_inv_eq_ringInverse`, `Complex.sub_conj`, `Complex.conj_im`, `HasDerivAt.star`, `HasDerivAt.ofReal_comp`,
`HasDerivAt.fun_sum`, `Finset.prod_range_succ`, `Finset.prod_range_succ'`, `Nat.add_mod_right`, `Nat.mod_eq_of_lt`,
`eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right`. Verified absent (`absent.lean`, `Unknown constant`, exit 1): `List.zip_rotate`.
Project names (compiled in the builds): `RBM.isUnit_sub_smul_of_isHermitian`, `BAMB_symm`, `BAMLoop_apply`, `BATheta_row_sum_pm`, `BAK_row_sum`,
`BAMss_pm_eq`, `BAPsi_isHermitian`, `uniqS_holds`, `retireS_holds`, `rotS_holds`.

## (d) Open issues and paper-delta candidates
- **Hand-off for K12 (`BAKward` on `BAKsol`).** `baK_ward` needs the `(Kn2sol)` clause for the family. `BAKsol_isKLoopS` (`RBM3D/BA/KSolve.lean:606`, merged
  T2368) discards the second conjunct of `BAKsolve` (`obtain ⟨K, hK, -⟩`), and `BAKsol` is the `Classical.choose` of the `IsKLoopS`-only existential
  (`BA/FlowPins.lean:281`), so `baK_ward ∘ BAKsol_isKLoopS` alone is not enough: `(Kn2sol)` for `BAKsol` is transferred from the `BAKsolve` witness by
  uniqueness (`uniqS_holds`, `retireS_holds`, `kernelFacts_one.entry`; as `baK_unique`, `KSolve.lean:568`). b8 compiles `BAKsolve d → BAKward d` this way.
- The compiled `baK_ward` instance is conditional on `BAKsolve` (the family). No other gate's pin enters; no external input.
- Paper-delta candidates: **T2369a** `lem_WI_K` (cited `[RBSO1D L3.17]`, `1_2:1034-1046`) is proved over a general kernel (`WardS`); the band proof is the
  argument (design §3 (d)). **T2369b** the `t = 0` step for `BAMLoop` is the entrywise resolvent identity `M - M^* = 2 i Im m M^* M` (`Im (E+m) = Im m`),
  not `BAMB_ward_row` alone (diagonal entry only; the ticket and design §3 (d) say "closes it"). **T2369c** `κ_t (m(+) - m(-)) = (W^d (1-t))⁻¹` from
  `m(-) = conj m(+)` alone; `‖m‖ = 1` is not needed (in BA `‖m‖ < 1` in general, N2 table `|m|`). **T2369d** Lean states the level-2 input as
  `∑_x K^{(2)}_{(+,-),(a,x)} = (W^d (1-t))⁻¹` (`WardS`), derived in BA from `(Kn2sol)` and `BATheta_row_sum_pm`; the paper's `n = 2` case of `(WI_calK)` is its
  consequence (`κ_t (m - m̄) = c_t`). **T2369e** `baK_ward` takes `(Kn2sol)` as a hypothesis (clause of `BAKsolve`); `3 ≤ L` is unused.

## Result
Targets 1-4 are built and committed on `t/T2369` at `424828c` (stage-1b commits `ce4a255`, `05384aa`, `424828c`); `git diff --stat main...t/T2369` (b1) touches only `RBM3D/Loop/KLWard.lean` and `RBM3D/BA/KWard.lean`; no `(a′)` correction was needed.
