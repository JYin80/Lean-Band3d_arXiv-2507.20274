Auditor model: claude-opus-5-5

# T2055 audit (round 2) — S3-04 `RBM3D/Induction/QopAlgebra.lean`
Written: Sat Oct  3 13:43:24 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2055-audit2`, detached at `f734825` (= `t/T2055`, repair of round 1).
`$S` = scratchpad `T2055/`. Round 1 RETURNed only for two missing compiled instances (`QopAlgebra_commutator_UN`, general `QopAlgebra_Qop_hasDerivAt`).

## Verdict
- Target 1 `stMollifierEx_holds (d : ℕ) : STMollifierEx d`: **PASS**.
- Target 2 (operator algebra of `Def:QtPt`): **PASS** (round-1 defect repaired; section 3).
- Ticket verdict: **PASS**. No dispatcher sign-off needed.

## 1. Statements
```
$ git diff --name-only main...HEAD ; git diff main...HEAD -- RBM3D/Induction/Step34Pins.lean | wc -l
RBM3D/Induction/QopAlgebra.lean
       0
$ grep -n '^import' RBM3D/Induction/QopAlgebra.lean
6:import RBM3D.Induction.Step34Pins
7:import RBM3D.Kernel.Evolution
$ sed -n '573p' RBM3D/Induction/QopAlgebra.lean ; sed -n 3p $S/aud2ax.lean   # compiled, exit 0 (section 4)
theorem stMollifierEx_holds (d : ℕ) : STMollifierEx d := by
example : ∀ d : ℕ, STMollifierEx d := stMollifierEx_holds
$ sed -n '574,575p' RBM3D/Induction/QopAlgebra.lean
  intro _ m Λ _
  refine ⟨(1 + 40 * ((d * m : ℕ) : ℝ)) * 6 ^ (d * m), 1 / 2, by positivity, by norm_num, ?_⟩
$ sed -n '345,346p' RBM3D/Induction/QopAlgebra.lean ; sed -n '136p;139p;339,340p' RBM3D/Induction/QopAlgebra.lean
def QopAlgebra_mollifier (d L m : ℕ) [NeZero L] (g : ℝ) (t : ℝ) (a : Fin (m + 1) → Zd d L) : ℂ :=
  ((qaPhi d L m a (qaU L g t) : ℝ) : ℂ)
private def qaY (g t : ℝ) : ℝ := 1 + g / Real.sqrt (1 - t)
private def qaU (L : ℕ) (g t : ℝ) : ℝ := (qaY g t)⁻¹ + (L : ℝ)⁻¹
private def qaPhi (d L m : ℕ) [NeZero L] (a : Fin (m + 1) → Zd d L) (u : ℝ) : ℝ :=
  Real.exp (-u * qaS a) / (qaZ1 L u) ^ (d * m)
```
Target 1: the theorem's type is exactly the merged pin `STMollifierEx d` (`Step34Pins.lean:518`, unchanged on the branch). Constants
`C = (1+40dm)6^{dm}`, `c = 1/2` are chosen after `m, Λ` and before `L, g` (pin's quantifier order), depend on `(d, m)` only.
`STMollifierProps` (`Step34Pins.lean:510`) has the four clauses `eq:suma1chi`, sup bound and `∂_t` bound of `eq:derv_Theta` (with hard
constants instead of `≺`: merged pin, T2041b), and differentiability on `[0,1)`. The mollifier is `rmk:choosechi` with a non-compact
exponential bump `exp(-u_t|x|_1)` at the smoothed scale `1/u_t` (T2041b); the pin is property-based, so this is admissible.
Clause 4 uses `deriv`; `QopAlgebra_mollifier_differentiableAt` (`:581`, any `t < 1`) shows `deriv` is the genuine two-sided derivative.

Target 2 vs `3_5:1204-1229` (`Def:QtPt`, `eq:sumzero_op`, `eq:suma1chi`, `eq:sum0PA`) and `Kernel/Evolution.lean` `ThetaN`/`UN` (`def:op_thn`, `def_Ustz`):
```
$ sed -n '601,603p;617,618p;629,631p;643,648p;786,789p;821,824p;871,875p;884,888p' RBM3D/Induction/QopAlgebra.lean   (excerpted)
QopAlgebra_Psum_Qop (ϑ) {t} (hϑ : ∀ a₁, ∑_{a 0 = a₁} ϑ t a = 1) A a₁ : STPsum (STQop ϑ t A) a₁ = 0
QopAlgebra_Qop_of_sumZero ϑ t {A} (hA : ∀ a₁, STPsum A a₁ = 0) : STQop ϑ t A = A
QopAlgebra_Psum_deriv (hsum : ∀ τ a₁, ∑ ϑ τ a = 1) {t ϑ'} (hd : ∀ a, HasDerivAt (fun τ => ϑ τ a) (ϑ' a) t) a₁ : STPsum ϑ' a₁ = 0
QopAlgebra_Qop_hasDerivAt (hA : ∀ a, HasDerivAt (A · a) (A' a) t) (hϑ : ∀ a, HasDerivAt (ϑ · a) (ϑ' a) t) a :
    HasDerivAt (fun τ => STQop ϑ τ (A τ) a) (STQop ϑ t A' a - STPsum (A t) (a 0) * ϑ' a) t
QopAlgebra_ThetaN_sumZero g (hL : 3 ≤ L) (hμ : ∀ i, ‖μs i‖ = 1) (ht0 : 0 ≤ t) (ht1 : t < 1) (hA : sum-zero) a₁ : STPsum (ThetaN d L g μs t A) a₁ = 0
QopAlgebra_UN_sumZero    g (hL : 3 ≤ L) (hμ) (ht0 : 0 ≤ t) (ht1 : t < 1) (hA : sum-zero) a₁ : STPsum (UN d L g μs s t A) a₁ = 0
QopAlgebra_commutator_ThetaN / _UN : STQop ϑ t (Op A) a - Op (STQop ϑ t A) a = Op (fun b => STPsum A (b 0) * ϑ t b) a - STPsum (Op A) (a 0) * ϑ t a
```
| Lean | paper | extra hypotheses | assessment |
|---|---|---|---|
| `Psum_Qop`, `Psum_mollifier` | `𝒫∘𝒬_t = 0`, `𝒫∘ϑ ≡ 1` | `eq:suma1chi` at `t` | equal |
| `Qop_of_sumZero` | `𝒬_t = id` on sum-zero | none | equal |
| `ThetaN_sumZero` | `eq:sum0PA` | `3≤L`, `‖μ_i‖=1`, `t∈[0,1)` | standing assumptions of `DefTHUST` (`t∈[0,1)`, `|m(σ)|=1`) |
| `UN_sumZero` | `𝒰` analogue | same, any `s` | general in `s` |
| `commutator_*` | `[𝒬_t, Θ]`, `[𝒬_t, 𝒰]` | none | pure linearity, general |
| `Qop_hasDerivAt` (`_const`: corollary) | `[∂_t, 𝒬_t]` via `∂_tϑ` | `HasDerivAt` of `A`, `ϑ` | general form |
| `Psum_deriv` | `𝒫 ∂_tϑ = 0` | `eq:suma1chi` ∀τ | equal |
No special-case adapter replaces a general target.

## 2. Vacuity, hidden hypotheses, cycles
```
$ grep -nE '^(structure|class)' RBM3D/Induction/QopAlgebra.lean ; echo "exit $?"
exit 1
```
- `STMollifierProps`/`STMollifierEx` are merged `def`s, not structures; clause 1 (sum one) forces `ϑ ≠ 0`, so no vacuous witness.
- Imports only merged modules (`Step34Pins`, `Kernel/Evolution`); no cycle. No external hypothesis (the pin has none), so no limit check is needed.

## 3. Compiled nonempty instances
```
$ for n in <18 public theorems>; do printf '%s %s\n' $n $(sed -n '899,1000p' QopAlgebra.lean | grep -cw $n); done
QopAlgebra_mollifier_sum 1               QopAlgebra_Psum_deriv 1             QopAlgebra_ThetaN_sumZero 1
QopAlgebra_mollifier_props 1             QopAlgebra_Qop_hasDerivAt 1         QopAlgebra_UN_sumZero 1
stMollifierEx_holds 5                    QopAlgebra_Qop_hasDerivAt_const 1   QopAlgebra_ThetaN_sub 0
QopAlgebra_mollifier_differentiableAt 3  QopAlgebra_col_sum_thetaKer 0       QopAlgebra_UN_sub 0
QopAlgebra_Psum_Qop 4                    QopAlgebra_col_sum_uKer 0           QopAlgebra_commutator_ThetaN 1
QopAlgebra_Qop_of_sumZero 1              QopAlgebra_Psum_mollifier 0         QopAlgebra_commutator_UN 1
$ sed -n '977,987p;988,996p' RBM3D/Induction/QopAlgebra.lean | grep -E '^  QopAlgebra|^    \(fun'
  QopAlgebra_commutator_UN 1 _ qaTheta (1 / 4) (1 / 2) A a
  QopAlgebra_Qop_hasDerivAt (A := fun τ _ => (τ : ℂ)) (A' := fun _ => 1)
    (fun _ => by simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp)
    (fun a => (QopAlgebra_mollifier_differentiableAt 3 3 1 le_rfl one_pos (by norm_num) a).hasDerivAt) a
```
- Target 1: `:901`, `:907` apply `stMollifierEx_holds 3 (by norm_num) m 1 one_pos` at `m = 1, 2`, `Λ = 1`; `:913` unpacks at `L = 5`, `g = 1`, `m = 2`;
  `:920` `QopAlgebra_mollifier_props 3 3 1 le_rfl one_pos` with explicit `C`, `c`. Nondegenerate, every hypothesis discharged. **OK.**
- Target 2 at `d = 3`, `L = 3`, `m = 1`, `g = 1`, `μ_i = 1`, `ϑ = qaTheta = QopAlgebra_mollifier 3 3 1 1` (`:925`), `t = 1/2`, `s = 1/4`:
  `Psum_Qop` :932, `Qop_of_sumZero` :937, `ThetaN_sumZero` :942, `UN_sumZero` :949 (sum-zero tensor `𝒬_t 1`), `commutator_ThetaN` :956,
  `Psum_deriv` :965 (`t = 0`), `Qop_hasDerivAt_const` :970, and (repair) `commutator_UN` :977, general `Qop_hasDerivAt` :988
  (`t = 0`, `t`-dependent `A τ ≡ τ`, `hA` and `hϑ` discharged). All compile in the module build (section 4). **OK.**
- `col_sum_*`, `*_sub`, `Psum_mollifier` are intermediate lemmas used inside the proofs, not ticket endpoints.

## 4. Build, axioms, hygiene, registry
```
$ lake build RBM3D.Induction.QopAlgebra 2>&1 | grep -E 'error|QopAlgebra.lean.*warning|Build completed'
Build completed successfully (3704 jobs).
$ grep -nE 'sorry|admit|native_decide|axiom' RBM3D/Induction/QopAlgebra.lean; echo "grep exit $?"
grep exit 1
$ lake env lean $S/aud2ax.lean > $S/aud2ax.out 2>&1; echo "exit $?"   # 18 public theorems + QopAlgebra_mollifier
exit 0
$ tr -s '\n' ' ' < $S/aud2ax.out | grep -o 'depends on axioms: \[[^]]*\]' | sort | uniq -c
  19 depends on axioms: [propext, Classical.choice, Quot.sound]
$ git log --oneline -1 $(git merge-base HEAD main); git diff --stat $(git merge-base HEAD main) main -- RBM3D RBM3D.lean | tail -1
5d1e6b1 T2045: merge S1-08 Induction/ScaleFacts, Induction/PerTimeCalc
                    (no Lean change on main since the branch point)
$ lake build RBM3D 2>&1 | grep -E '^error|Build completed'
Build completed successfully (3750 jobs).
$ printf 'import RBM3D\nimport RBM3D.Induction.QopAlgebra\n#assert_rbm_axioms\n' > $S/aud2pre.lean; lake env lean $S/aud2pre.lean > $S/aud2pre.out 2>&1; echo "exit $?"
exit 0
$ sed -n 1p $S/aud2pre.out; grep -n 'STMollifierEx\|premises found' $S/aud2pre.out; sed -n 56p $S/aud2pre.out | cut -c1-110
axiom audit: 1675 theorems, 637 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
51:  RBM.Gauss.Sizes.STMollifierEx: 2 [no certificate]
55:premises found by scanning: 49 (borrowed 2, owed 35, structural 12).
66: RBM.Gauss.Sizes.STMollifierEx,
registry: 5 borrowed + 43 owed + 23 structural; 22 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
$ grep -n 'STMollifierEx' RBM3D/Test/Axioms.lean | cut -c1-80
127:   `RBM.Gauss.Sizes.STMollifierEx, -- `rmk:choosechi`: existence of the moll
```
With this module, `STMollifierEx` is listed among the registered premises that carry nothing: its owed registry line
(`RBM3D/Test/Axioms.lean:127`) can go in the cleanup ticket (DECISIONS §16, §20). `Test/Axioms.lean` is untouched; the diff touches only
the sole writable file; no frozen signature changed.

## 5. Paper deltas
```
$ grep -n 'T2041b' docs/reports/T2041-prove.md | cut -c1-120 ; grep -c '2041' docs/paper-deltas.md
266:- `T2041b`: the mollifier of `rmk:choosechi` is pinned by its properties (`STMollifierProps`: sum one, sup bound, differentiable, `∂_t` b
0
```
- Smoothed scale, property-pinned mollifier, hard constants instead of `≺`: candidate `T2041b` (signed, T2041 report), cited by the prove report (d).
  Not yet numbered in `docs/paper-deltas.md` — dispatcher bookkeeping, not a T2055 defect.
- Hypotheses `3 ≤ L`, `‖μ_i‖ = 1`, `0 ≤ t < 1` of `eq:sum0PA`: standing assumptions of `DefTHUST`; no new delta.
- No new Lean/paper statement difference; coverage complete.

## 6. Observations (no effect on verdict)
- The general `Qop_hasDerivAt` instance (`:988`) is at `t = 0` with `A τ ≡ τ`, so `STPsum (A 0) = 0` and the `ϑ'` term has zero coefficient
  there; both hypotheses `hA`, `hϑ` are still discharged at nondegenerate data, and the `ϑ'` term is exercised by the `_const` instance (`:970`).
- `zeroModeSet`/`projMat` (named in the ticket) are not used; no target statement needs them (sum-zero is `STPsum A = 0`).
- Pin premises `3 ≤ d` and `g ≤ Λ` are unused in the proof; constants independent of `Λ` (allowed by the pin).
- Prove report: the repair section sits after (d) rather than updating b.5; b.9's `git diff --stat` (978 lines) predates the repair (999 lines).

## Required for resubmission
None.
