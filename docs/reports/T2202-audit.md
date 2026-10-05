Auditor model: claude-opus-5-5

# T2202 audit (UN-26a, `Universality/GUEPhase/Bootstrap.lean`), round 1
Time (date -u): Mon Oct  5 19:28:19 UTC 2026. Branch t/T2202 at d9f3538; audit worktree /Users/junyin/Lean_proof/RBM3D-wt/T2202-audit1 (detached).

## 1. Scope of the diff
```
$ git diff --name-status main...t/T2202
A	RBM3D/Universality/GUEPhase/Bootstrap.lean
$ grep -nE 'sorry|admit|native_decide|^axiom|set_option' Bootstrap.lean
38:set_option linter.style.longLine false
39:set_option linter.unusedSectionVars false
```
Only the sole writable file (`Test/Axioms.lean` untouched: allowed, registry adds nothing). No merged file changed, so no frozen signature touched.

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Universality.GUEPhase.Bootstrap   (0 warnings in log)
✔ [2509/2509] Built RBM3D.Universality.GUEPhase.Bootstrap (4.4s)
Build completed successfully (2509 jobs).
exit 0
$ lake env lean RBM3D/Universality/GUEPhase/Bootstrap.lean   -> exit 0
```
Scratch `pins.lean` (`import RBM3D` + the new module + check-file §2 copied verbatim + pin/rfl examples + `#print axioms` + `#assert_rbm_axioms`): exit 0, no error, no warning. 28 `#print axioms` lines, all `[propext, Classical.choice, Quot.sound]` (SBgue_apply, sum_SBgue_col/row, continuity_argument, ellT_eq_L, primBilGUE_add_left/right, primRhsGUE_sub, norm_primBilGUE_le, norm_primRhsGUE_le, sum_pow_mul_pow, K_bootstrap, finite_loopIdx, eq736, eventually_small, supOn_le, supOn_line1_le, mul_le_of_eq730, sqrt_mul_sqrt_le, supOn_nonneg, inv_mul_pow, eventually_rpow_le_of_neg, inst_eq736, inst_eq736_tight, inst_K_bootstrap, inst_norm_primBilGUE_le_one, inst_ellT_eq_L). Registry:
```
axiom audit: 6061 theorems, 2133 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: ...
```

## 3. Statements against the pins (check file §2), compiled
Examples appended to the verbatim check-file §2 (namespace `RBM.Univ.GUEPhase.T2202Check`), all elaborate:
```
example (d L : ℕ) [NeZero L] : SBgueV d L = SBgue d L := rfl
example (d L : ℕ) [NeZero L] (W : ℕ) : primBilGUEV d L W = primBilGUE d L W := rfl
example (d L : ℕ) [NeZero L] (W : ℕ) : primRhsGUEV d L W = primRhsGUE d L W := rfl
example : supOnV = RBM.Univ.GUEPhase.supOn := rfl
example : rhs745GV = RBM.Univ.GUEPhase.rhs745G := rfl
example : rhs746GV = RBM.Univ.GUEPhase.rhs746G := rfl
example : T2202_sum_SBgue_col := fun d L _ b => RBM.Univ.GUEPhase.sum_SBgue_col d L b
example : T2202_continuity_argument := fun hS => RBM.Univ.GUEPhase.continuity_argument hS
example : T2202_ellT_eq_L := fun hg ht h => RBM.Univ.GUEPhase.ellT_eq_L hg ht h
example : T2202_norm_primBilGUE_le := fun d L _ W K K' B B' I hI hK hK' hB hB' =>
  RBM.Univ.GUEPhase.norm_primBilGUE_le d L W K K' B B' I hI hK hK' hB hB'
example : T2202_norm_primRhsGUE_le := fun d L _ W K B I hI hK hB =>
  RBM.Univ.GUEPhase.norm_primRhsGUE_le d L W K B I hI hK hB
example : T2202_K_bootstrap := fun hS len => RBM.Univ.GUEPhase.K_bootstrap hS len
example : T2202_finite_loopIdx := fun d L _ n => RBM.Univ.GUEPhase.finite_loopIdx d L n
example : T2202_eq736 := fun d L W _ Kt => RBM.Univ.GUEPhase.eq736 d L W Kt
example : T2202_eventually_small := fun h => RBM.Univ.GUEPhase.eventually_small h
example : T2202_eventually_rpow_le_of_neg := fun ha hρ => RBM.Univ.GUEPhase.eventually_rpow_le_of_neg ha hρ
example : T2202_inst_bounds := RBM.Univ.GUEPhase.BootstrapCheck.inst_bounds
```
-> `lake env lean pins.lean`: exit 0. Every pin is proved with exactly its statement; every vocabulary def is `rfl`-equal.

## 4. Unpinned ported statements vs RBM2D `c9a24cf` (script `stmt.py`)
Normalization: `Z2 L↦Zd d L`, `(W:ℂ)^2↦(W:ℂ)^d`, `((W*L)^2:ℕ)↦((W*L)^d:ℕ)`, `((L:ℂ)^2)⁻¹↦((L:ℂ)^d)⁻¹`, binders `(L)↦(d L)`.
```
same-after-map: SBgue continuity_argument primBilGUE primRhsGUE GUEPhaseBootstrap_{two_le_length,length}_cutGlue{L,R}(_le)
  sum_pow_mul_pow finite_loopIdx LoopSet eventually_small supOn supOn_le rhs745G rhs746G supOn_line1_le
  mul_le_of_eq730 sqrt_mul_sqrt_le supOn_nonneg inv_mul_pow eventually_rpow_le_of_neg
DIFF only by the extra argument `d` (`SBgue L`↦`SBgue d L`, `primBilGUE L W`↦`primBilGUE d L W`):
  SBgue_apply primBilGUE_add_left primBilGUE_add_right primRhsGUE_sub norm_primBilGUE_le norm_primRhsGUE_le eq736
DIFF K_bootstrap: drift `d`↦`dk` only (as in the pin)
DIFF ellT_eq_L:
  2D: (ht : t < 1) (h : (L : ℝ) ^ 2 * (1 - t) ≤ 1) : Path.ellT L t = L
  3D: (hg : 0 ≤ g) (ht : t < 1) (h : (L : ℝ) ^ 2 * (1 - t) ≤ g ^ 2) : RBM.ellT L g t = L
NOT PORTED: eq736_detDom, stochDom_of_forall_highProb      NEW in 3D: sum_SBgue_col, sum_SBgue_row
$ git -C ../RBM2D diff --stat c9a24cf HEAD -- RBM2D/Universality/GUEPhase/Bootstrap.lean
 1 file changed, 8 insertions(+), 893 deletions(-)
```
Exactly the import-map changes and the ticket's changes; the non-ported set is exactly the ticket's. `primBilGUE` is the merged `treeEqRhs` (`Loop/TreeRep.lean:133`: `(W:ℂ)^d * ∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length, ∑ a b, K(cutGlueL) * SB d L g a b * K(cutGlueR)`) with `SB ↦ SBgue`, polarized. `ellT_eq_L` checked against `Defs/Params.lean:32` `ellT L g t = min (max (g/√|1−t|) 1) L`: hypotheses `0 ≤ g`, `t < 1` are the ones the ticket pins. No `3 ≤ d` anywhere.

## 5. Hidden hypotheses, vacuity, cycles
- No `structure`/`class` introduced; `LoopSet` is an `abbrev` of a subtype; no `Prop`-valued def. All hypotheses are explicit binders (`0 ≤ C`, `0 ≤ N`, `0 < A`, `0 < lam`, `0 ≤ g`, `t < 1`, `I.WF`).
- Imports: Mathlib (`Deriv.Inv`, `MeanValue`, `Complex.RealDeriv`, `Set.Finite.List`) and `RBM3D.Defs.{Lattice,Params,Domination}`, `RBM3D.Loop.TreeRep` only: all merged, no `import RBM3D`, no cycle.
- No external hypothesis (class G): only elementary limits `∀ᶠ N` in `eventually_small`, `eventually_rpow_le_of_neg`.
- Name clash: `git grep -nw "<kind> <name>" main -- RBM3D` for the 23 public stems: 0 hits each.

## 6. Compiled nonempty instances (namespace `RBM.Univ.GUEPhase.BootstrapCheck`, same file)
| target | instance | data / nondegeneracy |
|---|---|---|
| sum_SBgue_col/row | inst_sum_SBgue_col/row | d=3, L=3, b=0 |
| continuity_argument | inst_continuity_argument | S={1,2}, f i=i, g i=i+1, [0,1] |
| K_bootstrap | inst_K_bootstrap | S={0}, len 2, k≡1/100, λ≡16, C=N=A=1, ε=1/16 |
| norm_primBilGUE_le | _le_zero, _le_one | loopThree (WF, length 3, `rfl`), d=3,L=3,W=2, K=K'≡1, B≡1 (648 ≤ 3888) |
| norm_primRhsGUE_le | inst_norm_primRhsGUE_le | K≡1, B≡1, loopThree |
| eq736 | inst_eq736, inst_eq736_tight | N=216, n=2, [0,1], A=1; K≡0 (λ≡40000, ε=1/100) and the nonzero solution K=K₀/(1−N K₀ t) of K'=N K² (λ≡7000, ε=216/7000, 4n³Aε≈0.987<1), derivative proved via `primRhsGUE_const_len_two` |
| ellT_eq_L | inst_ellT_eq_L | L=4, g=1/2, t=63/64 (equality case) |
| finite_loopIdx | inst_finite_loopIdx | d=3,L=3,n=4; set contains loopThree |
| eventually_small / _rpow_le_of_neg | inst_* | n=2, τ'=1/4, τU=1/2; a=−1, ρ=1/2 |
| sum_pow_mul_pow, supOn_le, supOn_nonneg, inv_mul_pow, mul_le_of_eq730, sqrt_mul_sqrt_le, supOn_line1_le | inst_* | concrete reals (N=216, η≡1, [0,1]) |
| T2202_inst_bounds | inst_bounds | `norm_num` |
Every deterministic hypothesis is discharged in the term (WF by `rfl`, `0 < λ`, antitonicity `le_rfl`, continuity, derivatives, `0 ≤ g`, `t < 1`, (7.30), `4n³Aε<1`). No `N = 0`, empty index set or collapsed window; no open hypothesis left. All compile (§2).

## 7. Paper deltas
Lean/paper differences: (i) `ellT_eq_L` with coupling/floor (`L²(1−t) ≤ g²`) → candidate `T2202a`; (ii) `d`-form of (7.33)–(7.36) (`L^{-d}`, `W^d`, `N=(WL)^d`) → `T2202b`; bookkeeping `T2202c`; Lean structure (non-ported index-scale bootstraps, split, `dk`, explicit `d L W`) `T2202d`, extra Mathlib imports `T2202e` (prove report §(d), lines 246–250). All differences covered.

## 8. Observations (no effect on verdict)
- O1. The three algebraic identities `primBilGUE_add_left/right`, `primRhsGUE_sub` and `SBgue_apply` carry no hypotheses and have no dedicated instance; nothing to discharge (non-vacuous by form), and `primRhsGUE_sub` is used in the file's proofs.
- O2. Prove report flag F1 (section (a), line 26): the ticket's `τ_U ∈ {1/20, 1/10}` are the `𝔡` values of T2173's table, not its `τ_U` (≤ 1/79200); this affects the consumers' (UN-31/48–50) window bookkeeping only, not any statement here. For the dispatcher's attention.
- O3. Branch base 3fc9d03 is behind main b3c37aa; `git diff main...t/T2202` still lists only the sole writable file.
- O4. Three Mathlib imports beyond the ticket's example list; ticket allows "Mathlib"; reported as `T2202e`.

## Verdict
All targets 1–7 (and every ported vocabulary item): **PASS**. Ticket T2202: **PASS**. No dispatcher sign-off needed.
