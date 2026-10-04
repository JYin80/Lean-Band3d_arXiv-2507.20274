Auditor model: claude-opus-5-5

# T2113 audit (S1-25, `Green/MinorDiff`) — round 1, Sun Oct  4 05:57:44 UTC 2026

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2113-audit1`, detached at `t/T2113` = 2479590 (base 6187713).
Pin: RBM2D `Green/MinorDiff.lean` at `c9a24cf` (port; ST1-COMMON item 2 renaming R1/R2, `zt`/`mE`).

## 1. Scope of the diff
```
$ git diff --name-only main...HEAD
RBM3D/Green/MinorDiff.lean
$ grep -nE "sorry|admit|native_decide|^axiom|^private axiom" RBM3D/Green/MinorDiff.lean | wc -l
       0
```
Only the new sole writable file; `Test/Axioms.lean` untouched (allowed: registry lines only, none needed). No frozen signature touched.

## 2. Statement vs pin (independent script diff, auditor's own renaming)
```
$ git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Green/MinorDiff.lean > src2d.lean
$ sed -n 98,913p src2d.lean | perl -pe 's/Idx \(d\.L n\) \(d\.W n\)/Idx d (sz.L n) (sz.W n)/g;
    s/Sizes\.SeqΩ d\b/Sizes.SeqΩ sz/g; s/variable \{d : Sizes\} \{n : ℕ\}/variable {d : ℕ} {sz : Sizes d} {n : ℕ}/;
    s/spectralZ E t/zt E t/g; s/spectralM E/mE E/g;
    s/\b(minorDiff|gEnt|gFam|gInvFam|MinorGoodLe|greenSetDiagCentered|flucDiagSet|qRow|applyOps|BddMeas|greenSetMat) d\b/$1 sz/g' > a.lean
$ sed -n 96,911p RBM3D/Green/MinorDiff.lean > b.lean ; diff a.lean b.lean
331c331
< noncomputable def gFam (d : Sizes) (n : ℕ) (u : ℝ) (z : ℂ) (ω : Sizes.SeqΩ sz)
---
> noncomputable def gFam (sz : Sizes d) (n : ℕ) (u : ℝ) (z : ℂ) (ω : Sizes.SeqΩ sz)
336c336
< noncomputable def gInvFam (d : Sizes) (n : ℕ) (u : ℝ) (z : ℂ) (ω : Sizes.SeqΩ sz)
---
> noncomputable def gInvFam (sz : Sizes d) (n : ℕ) (u : ℝ) (z : ℂ) (ω : Sizes.SeqΩ sz)
```
The two residual lines are R1 (`(d : Sizes)` → `(sz : Sizes d)`), which my regex did not cover. The whole
ported body (816 lines, all 58 public declarations) is the RBM2D pin up to renaming: no hypothesis added,
dropped or weakened; quantifier order, `Ψ`-powers (`c Ψ^{p+|l|}`), budgets `M`, index ranges unchanged.
Key endpoint and the grading definition (verbatim):
```
905: theorem bddMeas_applyOps_minorDiff_flucDiagSet (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    (k : Idx d (sz.L n) (sz.W n)) (L : List (Bool × Idx d (sz.L n) (sz.W n))) :
    BddMeas sz (applyOps sz n L
      (minorDiff sz n (qList L) (flucDiagSet sz n u (zt E t) (mE E) k))) :=
224: def DiffBd (Ψ : ℝ) (I : Finset α) (M n : ℕ) (c : ℝ) (p : ℕ) (Y : Finset α → ℂ) : Prop :=
  ∀ (l : List α) (S : Finset α), l.Nodup → (∀ κ ∈ l, κ ∉ I) → l.length ≤ n →
    S.card + l.length ≤ M → ‖iterDeltaFam l Y S‖ ≤ c * Ψ ^ (p + l.length)
```
Ticket-named targets present: `deltaFam`, `shiftFam`, `iterDeltaFam`, `DiffBd` (+ `.le_self/.mono_I/_n/_M/_c/_p/.congr/.delta/.shift/.neg/.mul`),
`minorDiff_eq_iterDeltaFam`, `gFam`, `gInvFam`, `deltaFam_gFam_apply`, `bddMeas_applyOps_minorDiff_flucDiagSet`;
none dropped (58 names, matches the RBM2D `#print axioms` tail per the prove report b.6).
`d`-dependence: none in any statement (only the index type `Idx d …`); no `W`, `L`, weight, `∀ᶠ`. DECISIONS §29:
`|E| < 2`, `t < 1`, real `u` (no `0 ≤ u`) as D210. §30: no mass bound/weight appears.
Gain interface (ticket bullet): checked that S1-26 discharges it, not S1-25:
```
$ git -C ../RBM2D show c9a24cf:RBM2D/Green/MinorDiffCond.lean | grep -nE "^theorem minorDiffGainUpTo'_goodEvent|norm_minorDiff_greenSetDiagCentered_le|bddMeas_applyOps_minorDiff_flucDiagSet"
390:      refine le_trans (norm_minorDiff_greenSetDiagCentered_le hg hΨ0 hΨ1 k κ l'
668:    fun i => bddMeas_applyOps_minorDiff_flucDiagSet hE ht u (k i) (L i)
869:theorem minorDiffGainUpTo'_goodEvent (hE : |E n| < 2) (ht1 : t n < 1) {ε : ℝ} (hε : 0 ≤ ε)
```
The `q ≥ 1` layer check (one `Ψ` per `Δ`, per-layer `W^{-d/2}` at `d = 3`) is in prove report (a)(iii), numeric script output.

## 3. Hidden hypotheses, vacuity, cycles
- `DiffBd` is a `def … : Prop` that appears only in conclusions (closure lemmas, `diffBd_atom`), never as an unproved premise of an endpoint.
- The only premise structure is `MinorGoodLe` (merged, T2105 ec0e7d5), discharged concretely by `minorGoodLe_of_goodEvent_flow` in `check_hg` (below).
- Imports: only `RBM3D.Green.MinorGoodLe` (merged). `MinorDiffGainUpTo'` is not a hypothesis of any theorem here: no external hypothesis, no limit check owed.
- Registry pre-check (ST1-COMMON item 8):
```
$ lake build RBM3D      -> Build completed successfully (3856 jobs).
$ cat precheck.lean     -> import RBM3D / import RBM3D.Green.MinorDiff / #assert_rbm_axioms
$ lake env lean precheck.lean ; echo exit $?
axiom audit: 3457 theorems, 1228 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: ...
  RBM.Green.MinorDiffGainUpTo': 1 [no certificate]
exit 0      (lines matching "error": 0)
```
No new premise listed (MinorDiffGainUpTo' count 1 is T2105's).

## 4. Compiled nonempty instances (`MinorDiffInst`, same file)
Data: `d = 3`, `L = 3`, `W = 2` (`N = 216`), `lam = 1/2`, `n = 0`, `E = 0`, `u = t = 1/31`, `ω = 0`, `M = 3`, `Ψ = 2·(1/30)`,
five distinct sites `A..E` of `Z_6^3` (distinctness by `decide`).
```
private theorem check_hg :
    MinorGoodLe szM 0 (1 / 31) (zt 0 (1 / 31)) (mE 0) 0 (2 * (1 / 30)) 3 :=
  minorGoodLe_of_goodEvent_flow (E := 0) (by norm_num) zt_im_ne (by norm_num) (by norm_num)
    (by norm_num) goodEvent_omega_zero
theorem inst_endpoint :   -- norm_minorDiff_greenSetDiagCentered_le, k = A, rows B,C,D, m = 3 = M
  norm_minorDiff_greenSetDiagCentered_le check_hg (by norm_num) (by norm_num)
    siteA siteB [siteC, siteD] hAB (by simp [hBC, hBD, hCD]) (by simp [hCA, hDA]) (by decide)
theorem inst_bddMeas :    -- the S1-25 key statement, word3 = Q_B P_C Q_D, qList word3 = [B, D] (rfl)
  bddMeas_applyOps_minorDiff_flucDiagSet (E := 0) (t := 1 / 31) hE0 (by norm_num) (1 / 31) siteA word3
theorem inst_atom :       -- diffBd_atom at r = 2, I = {A,B}, T = {E}, budget 2, 2 + |T| = 3 = M
  diffBd_atom check_hg (by norm_num) (by norm_num) 2 {siteA, siteB} {siteE} 2 (by decide)
```
Coverage: every public declaration of the ported body is referenced in the instance section except
```
$ (per-name perl count over lines 931-1369) | awk '$1==0'
0 atomC_succ;0 atomC_zero;0 gFam_apply;0 gInvFam_apply;0 shiftFam_apply;
```
(all five are `rfl`/definitional unfolding lemmas, not endpoints). All deterministic hypotheses are proved;
no hypothesis of any instance is assumed. Nondegenerate: `N = 216`, three distinct rows, `M = 3`, `Ψ = 1/15 ≠ 0`,
`G ≠ m·1` and families non-constant (`inst_gEnt_nonconst`). Calculus lemmas instantiated on toy families on `Fin 3`.

## 5. Build and axioms (audit worktree)
```
$ lake build RBM3D.Green.MinorDiff 2>&1 | grep -E "error|Build completed"
Build completed successfully (3335 jobs).
$ lake env lean ax.lean   (one #print axioms per name: 58 ported + 35 MinorDiffInst.inst_*)
$ sed -E "s/.*depends on axioms: //" ax.out | sort | uniq -c
  91 [propext, Classical.choice, Quot.sound]
   1 [propext, Quot.sound]
   1 [propext]
'RBM.Green.diffBd_atom' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.norm_minorDiff_greenSetDiagCentered_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.bddMeas_applyOps_minorDiff_flucDiagSet' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.MinorDiffInst.inst_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.MinorDiffInst.inst_bddMeas' depends on axioms: [propext, Classical.choice, Quot.sound]
```
(build warnings shown are in other, merged files: `LDEQuad`, `FlucVanish`.)

## 6. Paper deltas
The paper has no minors/differences calculus (`3_5:33` states `(GavLGEX)`, `3_5:37` cites `[YY_25]` Lemma 4.1).
Lean's budget `M`, constants `atomC`, `minorDiffC`, `2^n`, side condition `Ψ ≤ 1`, pointwise-in-`ω` form are
covered by the proposed candidate **T2113a** (prove report (d)). No other Lean/paper difference found.

## 7. Observations (no verdict effect)
- At `ω = 0` the Green matrix is diagonal, so every `Δ` vanishes and the endpoint bound is trivially true there;
  the hypotheses are nonetheless all discharged at nondegenerate data. The numeric nonzero-`Δ` check is in (a)(iii).
- The constants are huge (`minorDiffC 2 = 2^91`, inherited from RBM1D/RBM2D): the bound is vacuous at realistic
  `Ψ` for `m ≥ 3`; this is the pin's statement, not a port defect (constants need not be optimal, CLAUDE.md §7).
- `RBM3D/Test/Axioms.lean:191` says `MinorDiffGainUpTo'` is "proved by S1-25"; it is S1-26
  (`MinorDiffCond.lean:869` above). Dispatcher fix of the registry comment.
- Branch base 6187713 is behind main 6f8ca5b (OptL2a, KLIndStepB); disjoint files.

## Verdict
All targets (58 ported declarations; endpoints `norm_minorDiff_greenSetDiagCentered_le`, `norm_greenSetDiagCentered_le`,
`diffBd_atom`, `deltaFam_gFam_apply`, `deltaFam_gInvFam_apply`, `minorDiff_eq_iterDeltaFam`,
`bddMeas_applyOps_minorDiff_flucDiagSet`, `DiffBd` closure lemmas): **PASS**. No dispatcher sign-off needed.
