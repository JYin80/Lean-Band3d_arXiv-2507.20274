Auditor model: claude-opus-5-5

# T2155 audit (round 1) — S5-22a `stExpInv_holds` — Sun Oct  4 19:06:58 UTC 2026

Branch `t/T2155` at `4fa82bf`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2155-audit1` (detached). Verdict: **PASS**.

## 1. Statement against the pin
```
$ sed -n 510p RBM3D/Evolution/ExpInv.lean   (branch)
theorem stExpInv_holds (d : ℕ) : STExpInv d := by
$ sed -n 441,445p RBM3D/Induction/Step5Pins.lean   (merged pin, main)
def STExpInv (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E u : ℝ), |E| < 2 → 0 ≤ u → u < 1 →
    ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (c : Zd d (sz.L n)),
      (∫ ω, Lloop sz n E u σ (fun i => a i + c) ω ∂(sz.seqP) = ∫ ω, Lloop sz n E u σ a ω ∂(sz.seqP)) ∧
      (∫ ω, Lloop sz n E u σ (fun i => -a i) ω ∂(sz.seqP) = ∫ ω, Lloop sz n E u σ a ω ∂(sz.seqP))
$ git diff main t/T2155 -- RBM3D/Induction/Step5Pins.lean | wc -l
       0
```
The target's type is literally the merged `Prop` `STExpInv d` for every `d` (ticket target 1: "the merged statement unchanged"); the pin is untouched. Quantifiers (`∀ sz n E u`, `|E|<2`, `0≤u<1`, `∀ σ a c`), both identities (shift `a+c`, reflection `-a`) and the measure `sz.seqP` are those of the pin. No added hypothesis.

## 2. Vacuity, hidden hypotheses, cycles
```
$ sed -n 511p;518-519p RBM3D/Evolution/ExpInv.lean
  intro sz n E u _ _ _ σ a c
      (fun M => expInv_loopFine_submatrix (sz.W n) T M (zt E u) σ a)
  exact ⟨key (Equiv.addRight c) (expInv_Aut_addRight _ c), key (Equiv.neg _) (expInv_Aut_neg _)⟩
$ grep -nE "^import" RBM3D/Evolution/ExpInv.lean
6:import RBM3D.Induction.Step5Pins
7:import RBM3D.Gauss.FineModel
$ sed -n 377,382p;461,467p RBM3D/Evolution/ExpInv.lean   (change-of-variables lemmas, signatures)
private theorem expInv_seq (φ : ∀ m, Idx d (sz.L m) (sz.W m) ≃ Idx d (sz.L m) (sz.W m))
    (hφ : ∀ m i j, svarF d (sz.L m) (sz.W m) (sz.lam m) (φ m i) (φ m j) =
      svarF d (sz.L m) (sz.W m) (sz.lam m) i j) :
    ∃ Φ : SeqΩ sz ≃ᵐ SeqΩ sz, MeasurePreserving Φ (seqP sz) (seqP sz) ∧
      ∀ (m : ℕ) (ω : SeqΩ sz),
        slice sz m (Φ ω) = expInv_Phi (φ m) (slice sz m ω) := by
private theorem expInv_integral_eq (n : ℕ) (u : ℝ) {T : Zd d (sz.L n) ≃ Zd d (sz.L n)}
    (hT : expInv_Aut (sz.lam n) T)
    (F F' : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ)
    (hF : ∀ M, F (M.submatrix (expInv_phi (sz.W n) T) (expInv_phi (sz.W n) T)) = F' M) :
    ∫ ω, F' (seqHflow sz n u ω) ∂(seqP sz) =
      ∫ ω, F (seqHflow sz n u ω) ∂(seqP sz) := by
  classical
$ sed -n 488,493p RBM3D/Evolution/ExpInv.lean
        simp_rw [hF]
    _ = ∫ ω, F (seqHflow sz n u (Φ ω)) ∂(seqP sz) := by
        simp_rw [hH]
    _ = ∫ ω, F (seqHflow sz n u ω) ∂(seqP sz) :=
        hΦ.integral_comp' (fun ω => F (seqHflow sz n u ω))

```
- The theorem has no hypothesis; no structure carries an extra field (the only structure in play is the merged `Sizes`). The proof is a genuine change of variables: a measure-preserving `Φ : SeqΩ sz ≃ᵐ SeqΩ sz` built from `Measure.infinitePi_map_piCongrLeft` (coordinate relabelling, variance preserved by `expInv_svarF_phi`) and `Measure.infinitePi_map_pi` with `gaussianReal_map_neg` (sign flips), then `MeasurePreserving.integral_comp'`; it does not rely on integrability (no `integral_undef` route), so it is not vacuous.
- Imports are merged modules only (`Induction/Step5Pins`, `Gauss/FineModel`), not `RBM3D`; no cycle. `|E|<2`, `0≤u<1` are unused (introduced as `_`); the statement is stronger than needed, recorded as T2155a. No external hypothesis, so no limit check needed.

## 3. Compiled nonempty instances
```
$ sed -n 530,542p RBM3D/Evolution/ExpInv.lean
example : STExpInv 3 := stExpInv_holds 3

/-- Both identities at the merged `sz0` (`L_0 = 4`, `W_0 = 32`, `λ_0 = 1/64`), `n = 0`, `E = 0`,
`u = 1/2`, `σ = (+,-)`, labels `a = (0, (0,1,2))` and shift `c = (1,1,1)` on `Z_4^3`. -/
example :
    let a : Fin 2 → Zd 3 (sz0.L 0) := ![fun _ => 0, fun k => ((k : ℕ) : ZMod (sz0.L 0))]
    let c : Zd 3 (sz0.L 0) := fun _ => 1
    (∫ ω, Lloop sz0 0 0 (1 / 2) ![true, false] (fun i => a i + c) ω ∂(sz0.seqP) =
        ∫ ω, Lloop sz0 0 0 (1 / 2) ![true, false] a ω ∂(sz0.seqP)) ∧
      (∫ ω, Lloop sz0 0 0 (1 / 2) ![true, false] (fun i => -a i) ω ∂(sz0.seqP) =
        ∫ ω, Lloop sz0 0 0 (1 / 2) ![true, false] a ω ∂(sz0.seqP)) :=
  stExpInv_holds 3 sz0 0 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num) ![true, false]
    ![fun _ => 0, fun k => ((k : ℕ) : ZMod (sz0.L 0))] (fun _ => 1)
$ grep -n "theorem sz0_values" -A1 RBM3D/Defs/Sizes.lean
267:theorem sz0_values : sz0.L 0 = 4 ∧ sz0.W 0 = 32 ∧ sz0.size 0 = 2097152 ∧ sz0.lam 0 = 1 / 64 := by
268-  refine ⟨rfl, rfl, ?_, ?_⟩
```
Both ticket instances are present: `STExpInv 3` and both identities at `sz0`, `n = 0`, `E = 0`, `u = 1/2`, `σ = (+,-)`, `a = (0,(0,1,2))`, `c = (1,1,1)` on `Z_4^3` (`L_0 = 4`, `W_0 = 32`, `λ_0 = 1/64`); every deterministic hypothesis (`|0|<2`, `0≤1/2`, `1/2<1`) is discharged by `norm_num`. Nondegenerate: nonzero shift, distinct labels, no empty index or collapsed window. They compile in the module build below.

## 4. Build, axioms, hygiene, diff scope
```
$ lake build RBM3D.Evolution.ExpInv   (audit worktree; error/warning lines of this module + tail)
⚠ [3775/3775] Built RBM3D.Evolution.ExpInv (3.7s)
warning: RBM3D/Evolution/ExpInv.lean:21:100: This line exceeds the 100 character limit, please shorten it!
Build completed successfully (3775 jobs).
exit=0
$ lake env lean RBM3D/Evolution/ExpInv.lean | grep -v longLine | grep -E "error|warning"; echo exit
exit=0   (no lines)
$ cat ax.lean; lake env lean ax.lean
import RBM3D.Evolution.ExpInv
#print axioms RBM.Gauss.Sizes.stExpInv_holds
example : RBM.Gauss.Sizes.STExpInv 3 := RBM.Gauss.Sizes.stExpInv_holds 3
'RBM.Gauss.Sizes.stExpInv_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|^axiom| axiom |native_decide" RBM3D/Evolution/ExpInv.lean | wc -l
0
$ git diff main...t/T2155 --name-only ; merge-base vs main
RBM3D/Evolution/ExpInv.lean
RBM3D/Test/Axioms.lean
merge-base: a438a51  main: a438a51
$ git diff main...t/T2155 -- RBM3D/Test/Axioms.lean | grep "^[-+] "
-   `RBM.Gauss.Sizes.STExpInv, -- translation and reflection invariance of `𝔼 𝓛^{(2)}`; S5-01 (T2138, DECISIONS §40: owed)
$ grep -nE "^(theorem|lemma|def|abbrev|instance)" RBM3D/Evolution/ExpInv.lean   (public declarations)
510:theorem stExpInv_holds (d : ℕ) : STExpInv d := by
$ grep -rn stExpInv_holds RBM3D (main) | wc -l
       0
```
All helpers are `private` with prefix `expInv_` (§3 (E)); the one public name `stExpInv_holds` is pinned and new on main. Only the two sole writable files change; the registry change is exactly the deletion of the owed line `STExpInv` (ticket: delete when the pre-check passes without it).

Registry pre-check (DECISIONS §20 (2)), reproduced in the audit worktree:
```
$ lake build RBM3D 2>&1 | grep -E "error" | head -2   (root without the new import: expected failure, hub adds the import at merge)
error: RBM3D.lean:201:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`:
error: build failed
$ awk (copy of RBM3D.lean, "import RBM3D.Evolution.ExpInv" after the last import) > Precheck.lean; diff RBM3D.lean Precheck.lean
198a199
> import RBM3D.Evolution.ExpInv
$ lake env lean Precheck.lean; echo exit; grep -c error; grep -o "registry: [^[]*"
exit=0
0
registry: 1 borrowed + 87 owed + 49 structural; 52 registered premise(s) carry nothing yet: 
```
With the merge-time root import, `inst_expInv` (`Step5Pins.lean:1035`, hypothesis `STExpInv 3`) is discharged by a proved theorem and the root audit passes. The full `lake build` is the hub's merge step 5.

## 5. Paper deltas
- T2155a (proposed in the prove report (d)): the pin carries `|E|<2`, `0≤u<1`, which the proof does not use; the paper (`3_5:2196-2200`) uses the invariance informally without them. Covered.
- T2155b (proposed): the identity is for the merged single-time flow `H_u = √u X` (`seqHflow`), the model fixed for the pin (D323/T2134i records the pin itself in `docs/paper-deltas.md:1281`). Covered.
No other Lean/paper statement difference: the target is the merged pin verbatim.

## Observations (no effect on verdict)
- Prove report (b) shows the plain worktree `lake build` failing at the root assertion; this is the expected pre-merge state explained there and reproduced above, not a defect.
- The module emits one longLine linter warning (`ExpInv.lean:21`); style only.

## Verdict
| Target | Verdict |
|---|---|
| `stExpInv_holds (d : ℕ) : STExpInv d` | **PASS** |

No dispatcher sign-off needed. Hub: add `import RBM3D.Evolution.ExpInv` after the last import of `RBM3D.lean` at merge.
