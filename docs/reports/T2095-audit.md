Auditor model: claude-opus-5-5
# T2095 audit (round 1) — ST2-28a `Induction/HierAlgebra`, `Induction/HierarchyN`
Written Sun Oct  4 02:03:58 UTC 2026. Audit worktree `RBM3D-wt/T2095-audit1`, detached at `t/T2095` = `5f3813e`.
Ticket inputs: T2095.md (incl. Amend 1), DECISIONS §32, paper-delta D149, RBM2D `c9a24cf` sources.

## 1. Build, axioms, hygiene, touched files
```
$ lake build RBM3D.Induction.HierAlgebra RBM3D.Induction.HierarchyN | grep -E "error|Induction/Hier|Build completed"
info: HierAlgebra.lean:893..902: primBil_add_add primRhs_sub sum_primBilLen sum_primBilLenR sum_couplingLen
      couplingLen_eq_zero_outside primRhs_split norm_primBil_le couplingLen_two_Kval_eq_thetaOp
      loopDrift_sub_K_deriv_n  -- each: depends on axioms: [propext, Classical.choice, Quot.sound]
info: HierarchyN.lean:251..253: hierarchyN_of_loopGenN hierarchyN_two loopGenNForm_two_of_loopGenN2
      -- each: depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3751 jobs).   exit=0   (no error lines)
$ lake build      # full library in the audit worktree (root does not yet import the new modules)
info: RBM3D.lean:135:0: axiom audit: 2988 theorems, 1138 definitions, 0 axioms in `RBM` ...
Build completed successfully (3836 jobs).   exit=0
$ lake env lean scratch/precheck.lean   # import RBM3D + both modules; #assert_rbm_axioms; #print axioms of instances
axiom audit: 3017 theorems, 1145 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
105:  RBM.Ind.STLoopGenNForm: 2 [no certificate]
'RBM.Ind.HierAlgebra_check_norm_primBil_le' / _primBil_value / _primRhs_split / _couplingLen_two / _algebra /
'RBM.Ind.HierAlgebra_check_loopDrift_sz0' / 'RBM.Ind.HierarchyN_check_sz0' / _check_two_sz0 /
'RBM.Ind.HierarchyN_check_loopGenNForm_two_sz0' / primBil_add_left / primBil_add_right / STllPairN_eq_treeEqRhs
   -- each: depends on axioms: [propext, Classical.choice, Quot.sound]                      exit=0
$ grep -nwE "sorry|admit|axiom|native_decide" <both files> | grep -v "#print axioms"
(no hits)
$ git diff --name-status main...HEAD
A	RBM3D/Induction/HierAlgebra.lean
A	RBM3D/Induction/HierarchyN.lean
M	RBM3D/Test/Axioms.lean     (one added line in `owedProps`: `RBM.Ind.STLoopGenNForm, -- ... ST2-28 ... §32`)
$ git grep -nw <15 new public names> main -- 'RBM3D/*.lean' | wc -l    → 0 for every name
$ grep -nE "Z2|\^ 2" <both files>
HierAlgebra.lean:14:  (docstring: renaming rules)
HierAlgebra.lean:258, 307:  (I.length : ℝ) ^ 2   -- number of cut pairs, dimension-free
```
Only sole writable files touched; no frozen signature modified; imports are `Step34Pins`, `DriftAlgebra`, `LoopStep` (not `RBM3D`).

## 2. Statements (normalized script diff vs RBM2D `c9a24cf`)
Normalization: drop `(W : ℕ)`/`(L W : ℕ)`/`(d L W : ℕ)` binders, `Z2 L→Zd d L`, `(W:ℝ)^2→^d`, `(L:ℝ)^2→^d`,
`primBil* L W→primBil* d L W g`, `KLoop.primRhs L W→treeEqRhs d L W g`.
```
$ python3 sigs.py HA2.lean(c9a24cf) RBM3D/Induction/HierAlgebra.lean
SAME  primBil_self primBil_add_left primBil_add_right primBil_add_add primRhs_sub sum_primBilLen
SAME  sum_primBilLenR sum_couplingLen couplingLen_eq_zero_outside primRhs_split norm_primBil_le
DIFF  couplingLen_two_Kval_eq_thetaOp
   2D: ... (hL : 3 ≤ L) (E : ℝ) (hE : |E| ≤ 2) (u) (hu0 : 0 ≤ u) (hu1 : u < 1) (D) {k} [NeZero k] (hk : 2 ≤ k) σ a :
       couplingLen .. 2 (KLoop.Kcal L W E u) D (loopOf σ a) = thetaSig L E σ u (fun v => D (loopOf σ v)) a
   3D: ... (g : ℝ) (hL : 3 ≤ L) (E : ℝ) (hE : |E| ≤ 2) (u) (hu0) (hu1) (D) {k} (hk : 2 ≤ k) σ a :
       couplingLen d L W g 2 (KLK d L g W E u) D (loopOf σ a) = ThetaN d L g (fun i => mSigma E (σ i)) u (..) a
DIFF  loopDrift_sub_K_deriv_n
   2D: (L W) (E) (hL : 3 ≤ L) (hE : |E| < 2) u hu0 hu1 (M : Matrix (Idx L W) ..) (k) [NeZero k] (hk : 2 ≤ k) σ a :
       (llPairN + egtN) - deriv (Kcal · (loopOf σ a)) u = thetaSig .. (lkTensor ..) a + Σ_{Icc 3 k} ksimLK + elklkN + egtN
   3D: {d} (sz : Sizes d) (n) (E) (hE : |E| < 2) u hu0 hu1 (M : Matrix (Idx d (sz.L n) (sz.W n)) ..) {k} (hk : 2 ≤ k) σ a :
       (STllPairN + STegtM) - deriv (STKloop n E · σ a) u = ThetaN .. (sz.lam n) .. (STLKIM ∘ loopOf σ) a
         + Σ_{Icc 3 k} STksimLKM + STelklkM + STegtM
```
Reading of the DIFFs: `couplingLen_two…` gains a free coupling `g` and drops `[NeZero k]` (both weaken hypotheses);
`loopDrift…` is in the D149 `∀ sz n`, `g = sz.lam n` shape with merged `ST*` vocabulary (`3 ≤ L` from
`Sizes.three_le_L`, `Defs/Sizes.lean:145`; `STKloop = KLK … (KLloopOf σ a)`, `Induction/Defs.lean:64`). Both are
the ticket's mandated shape, not special cases.

`HierarchyN d`, `STLoopGenNForm d` (HierarchyN.lean:42, :56) vs merged `HierarchyN2`, `LoopGenN2`
(`Path/DriftAlgebra.lean:62, :75`): identical binder prefix `∀ sz n E, |E|<2 → ∀ u, 0≤u → u<1 → ∀ M, M.IsHermitian →`;
then `∀ k, 2 ≤ k → ∀ σ a` in place of `∀ a₁ a₂`; LHS `genMat … (loopOf σ a) − deriv (STKloop · σ a) u`; RHS
`ThetaN(STLKIM) + Σ_{l∈Icc 3 k} STksimLKM l + STelklkM + STegtM` = the merged `STgDriftN` body
(`Step2Defs.lean:784-792`) at `H = M`. Against the paper: `(eq_L-Keee)` `3_5:73` has drift
`[𝒦^{(2)}∼(𝓛−𝒦)] + Σ_{l=3}^n [𝒦^{(l)}∼(𝓛−𝒦)] + 𝓔^{(𝓛−𝒦)×(𝓛−𝒦)} + 𝓔^{G̃}`; the first term is
`Θ^{(n)}_{t,σ}∘(𝓛−𝒦)` (text after `def_Ustz`), and `ThetaN`/`thetaKer = μ S Θ_{tμ}` (`Kernel/Evolution.lean:52-62`)
is `(def:op_thn)` `3_5:109` with `μ_i = m(σ_i)m(σ_{i+1})` cyclic. Index range `l ∈ [3,k]`, loop length `k ≥ 2`,
`W^d` weight, `|E|<2`, `u ∈ [0,1)`: all match. Amend 1 pins: `def STLoopGenNForm (d : ℕ) : Prop` ✓,
`theorem hierarchyN_of_loopGenN (d : ℕ) : STLoopGenNForm d → HierarchyN d` ✓ (verbatim), `n = 2` reductions
`hierarchyN_two : HierarchyN d → HierarchyN2 d` ✓ and `loopGenNForm_two_of_loopGenN2` (from `LoopGenN2 d`) ✓.
Class b: `W^2→W^d`, `L^2→L^d` (`card_Zd`), `sum_nnnorm_SB_row d L g`; remaining `^2` is `(I.length)^2` (pair count).

## 3. Vacuity, hidden hypotheses, cycles
- No structures/classes introduced; all hypotheses are in signatures. `STLoopGenNForm` is the only non-derived
  `Prop` hypothesis, owed to ST2-28 per DECISIONS §32 and registered (precheck line 105: 2 theorems rest on it).
- Non-vacuity of `STLoopGenNForm`: at `k = 2`, `σ = (+,−)` it is proved from the merged, proved `LoopGenN2`
  (`HierarchyN_check_loopGenNForm_two_sz0` uses `loopGenN2 3`, unconditional); for `k = 3` the preflight's
  numeric check (prove report (a)(ii), d=3 L=3 W=2 g=1/2, random Hermitian M) gives residual ≤ 4.2e-17 with all
  terms nonzero — the concrete check for the owed hypothesis.
- No cycle: `HierarchyN` imports only `HierAlgebra`; `HierAlgebra` imports merged `Step34Pins`, `DriftAlgebra`,
  `LoopStep`. `loopDrift_sub_K_deriv_n` and `couplingLen_two…` are unconditional (axioms above).

## 4. Compiled nonempty instances (all compile; axioms above)
| endpoint | instance | data | kept hypotheses |
|---|---|---|---|
| norm_primBil_le | HierAlgebra_check_norm_primBil_le (+ _primBil_value = 216 ≠ 0) | d=3,L=3,W=2,g=1/2, I0=((+,−),(0,0)), F=G=1, B=1 | none |
| primRhs_split | HierAlgebra_check_primRhs_split | same, ∀ K D | none |
| couplingLen_two_Kval_eq_thetaOp | HierAlgebra_check_couplingLen_two | d=3,L=3,W=2,g=1/2,E=0,u=1/2,k=3,σ=(+,−,+),a=(0,1,2) | none |
| primBil_add_*, primRhs_sub, sum_*, couplingLen_eq_zero_outside | HierAlgebra_check_algebra | I0, range 4, lK=5 | none |
| loopDrift_sub_K_deriv_n | HierAlgebra_check_loopDrift_sz0 | sz0 n=0 (L=4,W=32,lam=1/64), E=0,u=1/2,M=1,k=3,σ=(+,−,+),a=(0,1,2) | none |
| hierarchyN_of_loopGenN | HierarchyN_check_sz0 | same, M=1 Hermitian | `STLoopGenNForm 3` (owed pin, ST2-28) |
| hierarchyN_two | HierarchyN_check_two_sz0 | sz0 n=0, a=(0,1) | `HierarchyN 3` (= conclusion of the owed route) |
| loopGenNForm_two_of_loopGenN2 | HierarchyN_check_loopGenNForm_two_sz0 | sz0 n=0, a=(0,1) | none (`loopGenN2 3`) |
```
$ #print RBM.Gauss.SizesInst.sz0
def RBM.Gauss.SizesInst.sz0 : RBM.Gauss.Sizes 3 :=
{ L := fun n => 4 * (n + 1), W := fun n => (2 * (n + 1)) ^ 5, lam := fun n => ((2 * (↑n + 1)) ^ 6)⁻¹, ... }
```
No `N = 0`, empty index, collapsed window, `False` premise, or large witness. All deterministic hypotheses
(`|E|<2`, `0≤u<1`, `3≤L`, `2≤k`, Hermitian, WF, `NeZero`) are discharged.

## 5. Paper-delta coverage
| Lean/paper difference | coverage |
|---|---|
| `hierarchyN` only conditional on `STLoopGenNForm` | T2095a (proposed), DECISIONS §32 |
| `Θ^{(n)}_{t,σ}` is the merged `ThetaN` (`μ S Θ_{tμ}`, `cycProd`) | T2095b (proposed) |
| `∀ sz n`, `g = sz.lam n`, merged `ST*` vocabulary | D149, D150 (existing) |
| `couplingLen_two…` with free `g`, `|E| ≤ 2`, no `[NeZero k]`; `loopDrift…` without Hermitian | weaker hypotheses than needed by the paper's use; no statement loss |
| `norm_primBil_le` constant `W^d n² L^d` | Lean auxiliary bound, no paper counterpart claimed |

## 6. Observations (no verdict effect)
- O1: `primBil_self`, `STllPairN_eq_treeEqRhs` (`rfl` lemmas) have no dedicated instance; they are definitional
  unfoldings, used inside proofs; not endpoint theorems of the ticket.
- O2: `STllPairN` duplicates the `treeEqRhs (loopL …)` part of merged `Path/OneStep.lean:539` `loopDrift`
  (different vocabulary: `STLIM`); ST2-28 may want a bridge lemma.
- O3: Prove report (a′) records that the general-`n` `STLIM … STegtM` already existed in `Step2Defs`; the
  implementation uses them (no restatement), consistent with the ticket.

## Verdicts
- HierAlgebra targets (`primBil` family, `primRhs_split`, `norm_primBil_le`, `couplingLen_two_Kval_eq_thetaOp`,
  `loopDrift_sub_K_deriv_n`): **PASS**.
- `STLoopGenNForm`, `HierarchyN`, `hierarchyN_of_loopGenN` (Amend 1 form): **PASS**.
- `n = 2` reductions `hierarchyN_two`, `loopGenNForm_two_of_loopGenN2`: **PASS**.
**Overall: PASS.** No dispatcher sign-off needed (the conditional form was already decided in DECISIONS §32).
