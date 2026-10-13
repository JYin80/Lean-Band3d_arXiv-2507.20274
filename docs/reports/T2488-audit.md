Auditor model: claude-opus-5-5

# T2488 audit, round 1 (L3d1 `Graph/BAAnpLift`), Tue Oct 13 04:57:47 UTC 2026

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2488-audit1`, detached at `t/T2488` = 63baa94a, merge-base `main` 2cc78196.
No split (388 lines; `BAAnpLiftB` unused): all targets 1-5 are delivered here. Start decision: L3d2b-2 merged at 2cc78196, so 4 (b) is included.
`$S` = scratchpad `.../scratchpad/T2488`.

## 1. Build, axioms, diff, hygiene
```text
$ lake build RBM3D.Graph.BAAnpLift
exit=0   (warnings only from merged files, e.g. Defs/Tail.lean, Green/LDEQuad.lean; none in BAAnpLift.lean)
$ lake build            (branch root, unchanged RBM3D.lean)
info: RBM3D.lean:574:0: axiom audit: 14511 theorems, 4545 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4342 jobs).
EXIT=0
$ cat $S/registry.lean ; lake env lean $S/registry.lean      (root + new module, registry check; no source edited)
import RBM3D
import RBM3D.Graph.BAAnpLift
#assert_rbm_axioms
exit=0
axiom audit: 14516 theorems, 4547 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms: ...
$ grep -cE "BAAnpAuxG|BAAnpKeyGhG|BAAnpG|LWXigL|LWLoop2gL|BAAnpLift" $S/registry.out   -> 0   (no new premise in any ledger)
$ #print axioms (in $S/audcheck.lean)
'RBM.Graph.baAnpKeyGhG_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baAnpG_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baAnpAuxG_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baLWMoment_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baLWMomentExp_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
$ git diff --name-status main...t/T2488
A	RBM3D/Graph/BAAnpLift.lean
$ grep -cwE "sorry|admit|axiom|native_decide" RBM3D/Graph/BAAnpLift.lean   -> 0
$ git grep -l "RBM3D.Graph.BAAnpLift" -- RBM3D RBM3D.lean (outside the file)   -> none
$ grep -c BAShapePath RBM3D/Graph/BAAnpLift.lean   -> 0 ;  grep -c inductive -> 0
```
Only the sole writable file is touched; `RBM3D.lean` (import line) is left for the hub (§3 (A) 4); `Test/Axioms.lean` unchanged.

## 2. Statements against the pins (script)
```text
$ lake env lean $S/audcheck.lean   (= docs/tickets/checks/T2488-check.lean + `import RBM3D.Graph.BAAnpLift`,
                                    the two shape `example : Prop` renamed `def Shape1`/`def Shape2` by script, plus:)
example : T2488_AnpAuxG := RBM.Graph.baAnpAuxG_holds
example : T2488_MomentClosed := RBM.BA.baLWMoment_closed
example : T2488_MomentExpClosed := RBM.BA.baLWMomentExp_closed
example : Shape1 = (∀ d : ℕ, RBM.Graph.BAAnpKeyGhG d) := rfl
example : Shape2 = (∀ d : ℕ, RBM.Graph.BAAnpG d) := rfl
example : Shape1 := RBM.Graph.baAnpKeyGhG_holds
example : Shape2 := RBM.Graph.baAnpG_holds
exit=0 ; grep -c error -> 0
baAnpAuxG_holds : ∀ (d : ℕ), BAAnpAuxG d
baLWMoment_closed : ∀ (d : ℕ), BALWMoment d
baLWMomentExp_closed : ∀ (d : ℕ), BALWMomentExp d
baAnpKeyGhG_holds : ∀ (d : ℕ), BAAnpKeyGhG d
baAnpG_holds : ∀ (d : ℕ), BAAnpG d
```
The three binding pins are matched by type ascription (definitional identity: `T2488_* := ∀ d, <merged def> d`); the two shapes by `rfl`.
Target 3 is the merged `BAAnpAuxG` (`BAAuxGraph2B:865`) with no second `Prop` (X1-C4).

Band comparison of the two new statement defs (substitution only):
```text
$ diff <(sed -n 389,407p RBM3D/Graph/LWPins.lean) <(sed -n 73,87p RBM3D/Graph/BAAnpLift.lean)
1c1  < def LWAnpKeyGh (d : ℕ) : Prop :=                      > def BAAnpKeyGhG (d : ℕ) : Prop :=
3c3  < ∀ Γ : RBM.Graph.NGraph p q, ...                         > ∀ Γ : NGraph p q, ...
5,6c5,6
<         ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
<           ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
>         ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
>           ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
9,10c9,10
<                 LWXi sz (STflowE z) t Φ ξ →
<                 Prec sz (U := fun n => (Fin p → Zd d (sz.L n)) × (Fin p → Zd d (sz.L n)))
>                 LWXigL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t Φ ξ →
>                 PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin p → Zd d (sz.L n)) × (Fin p → Zd d (sz.L n)))
12c12
<                   (fun n ab _ => ((((sz.W n : ℕ) : ℝ) ^ d) * etaT (STflowE z n) (t n))⁻¹ ^ q *
>                   (fun n ab _ => ((((sz.W n : ℕ) : ℝ) ^ d) * (baFMz sz z).eta n (t n))⁻¹ ^ q *
16,19d15  (trailing blank line / next docstring of LWPins only)
$ diff <(sed -n 409,424p LWPins.lean) <(sed -n 193,206p BAAnpLift.lean)  -> the same five substitutions (lines 1,3,5-6,9-10,12), nothing else
```
Hypotheses, quantifier order (`∃ c` before `𝔠 sz z`), losses `(W^d η)^{-q}`, `Φ(0)^{ord-n_ngh}`, path factor, ranges: the band's; only law, `η`, flow, horizon change.

## 3. Hidden hypotheses, vacuity, cycles
```text
$ grep -nE "^(theorem|lemma|def|private|instance|abbrev|structure|inductive|class|example)" RBM3D/Graph/BAAnpLift.lean
73:def BAAnpKeyGhG (d : ℕ) : Prop :=
94:private theorem BAAnpLift_core {d p q : ℕ} {Γ : NGraph p q} (hdet : AnpDetGhAt d Γ) :
182:theorem baAnpKeyGhG_holds : ∀ d : ℕ, BAAnpKeyGhG d := by
193:def BAAnpG (d : ℕ) : Prop :=
211:theorem baAnpG_holds : ∀ d : ℕ, BAAnpG d := by
229:theorem baAnpAuxG_holds : ∀ d : ℕ, BAAnpAuxG d := by
255:theorem baLWMoment_closed : ∀ d : ℕ, BALWMoment d := fun d => baLWMomentOfAnp_closed d (baAnpAuxG_holds d)
258:theorem baLWMomentExp_closed : ∀ d : ℕ, BALWMomentExp d := fun d => baLWMomentExp_of_anp d (baAnpAuxG_hold...
287:private theorem BAAnpLift_zeta0 (hL : LWLoop2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) Φb)
298/312/327/364/378: example ...
```
- Every public theorem has the single binder `d : ℕ`: no unproved `Prop` premise (`LWXigL`, `BAAnpAuxG`, `LWLoop2gL` appear only
  inside the statement defs, as a conclusion, in the private core/helper, or in examples). No new structure; no structure field carries a hypothesis.
- Proof chain: `anpDetGh_holds` (merged, model-free) -> private core (law/carrier generic; reads only `size → ∞` and `η > 0`) ->
  `baAnpKeyGhG_holds` (`hflow.1.2.2.1`, `BAExp14a_eta_pos`) -> `baAnpG_holds` -> `baAnpAuxG_holds` (`baAuxNested_holds`) -> closures through the
  merged `baLWMomentOfAnp_closed` (`BAMomentExpGen:189`) and `baLWMomentExp_of_anp` (`BAMomentExpGenB:1207`). All dependencies are merged on
  2cc78196; nothing imports the new file, so no cycle. Consumer antecedents (`BALWMomentOfAnp d := BAAnpAuxG d → BALWMoment d`, `BAMomentGenB:362`;
  `BALWMomentExpOfAnp`, `BAMomentExpGenB:1202`) read exactly the merged `BAAnpAuxG`.
- UBA-C1: `grep -nE "sz\.lam|withLam|Sizes|gK"`: `sz.lam`, `gK` 0 code hits; `withLam` only in the law `Sizes.seqP (sz.withLam 0)` (lines 81, 82,
  201, 202, 277, 355), `Sizes` only as the type `Sizes d` (77, 95, 197), `Sizes.seqP`, `Sizes.tendsto_size` (109) and `open` lines. No crossing.
- External hypotheses: none in targets 1-4.

## 4. Compiled nonempty instances (all five compile in the module build above)
| target | line | data | hypotheses left (other gates' pins) |
|---|---|---|---|
| 3 `baAnpAuxG_holds 3` | 298 | `baPQ`, `p = 2`, `n_M = 1`, `ξ = baZetaVar sz0 zSeq (1/2) ρ0 12` | `LWLoop2gL`, entry law `‖G_t-M‖ ≺ W^{-1/20}` |
| 1 `baAnpKeyGhG_holds 3` | 312 | `anpKey_oneEdge` (`p=1, q=0`), same `ξ` | same |
| 2 `baAnpG_holds 3` | 327 | `anpKey_oneEdge`, `NoGhost` proved inline | same |
| 4 (a) `baLWMoment_closed 3` | 364 | `p = 2`, `ε₀ = 1/10`, `BAMomentExpGen_Ψ0/Φ0` | `STInitialGT2gL`, `LWLoop2gL` |
| 4 (b) `baLWMomentExp_closed 3` | 378 | `p = 2`, `ε₀ = 1/20`, `Ψ0`, `ℓ_t`, any `D > 0` | `STInitialGT2gL`, `LWLoopExpgL` |
Common data: `d = 3`, `sz0`, `flow_sz0` (`κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`), `zSeq`, `t ≡ 1/2` with `half_lt_t0`, class constants
`(1/10, 2, 2, 1, 1)`, `LWPsiAll` discharged (`BAAuxGraph2B_psiAll`, `BAMomentExpGen_psiAll0`), windows discharged; `BAAnpAuxG 3` is no hypothesis.
```text
$ cat $S/inst2.lean ; lake env lean $S/inst2.lean
example : BAAtomInst2.baPQ.g.nM = 1 := by decide
example : sz0.L 0 = 4 ∧ sz0.W 0 = 32 := by decide
exit=0
```
Nondegenerate: `N_0 = (4·32)^3 = 2^21`, nonempty graphs, `p ≥ 1`, no `False` premise; every deterministic hypothesis discharged at the data.
The remaining hypotheses are pins owned by other gates (allowed by §4 step 2); the entry law's limit check is in the prove report (a)(ii)
(T2470 script, `Bctl^{1/4} = W^{-0.699..-0.745}` vs `W^{-1/20}`).

## 5. Paper deltas
- `BAAnpKeyGhG`, `BAAnpG`: the band `LWAnpKeyGh`, `LWAnp` under a pure carrier substitution (diff §2); the band-level differences
  (nested form of `lem:Anp`) are covered by D100 (`docs/paper-deltas.md:416`); the BA carrier form `ζ` by D686 (`:1650`, T2435a-d).
- G4 at BA: the non-centre summation of `B:494` sits in G3, not in `BAAnpAuxG`: proposed as `T2488a` (prove report (d)). Closures: compositions, no delta.
Coverage complete.

## 6. Verdicts
| target | verdict |
|---|---|
| 1 `BAAnpKeyGhG`, `baAnpKeyGhG_holds` | PASS |
| 2 `BAAnpG`, `baAnpG_holds` | PASS |
| 3 `baAnpAuxG_holds` (= `T2488_AnpAuxG`) | PASS |
| 4 (a) `baLWMoment_closed` (= `T2488_MomentClosed`) | PASS |
| 4 (b) `baLWMomentExp_closed` (= `T2488_MomentExpClosed`) | PASS |
| 5 instances | PASS |

Observations (no RETURN):
- O1. The file uses `open private` for 11 private names of merged files (`AnpKey` 2, `BAAuxGraph2B` 5, `BAMomentExpGen` 4) instead of the
  ticket's "re-derived" instance data; builds are clean, but renaming one of them breaks this leaf (recorded in the prove report (d)).
- O2. The optional target 5 (i) instance at a reached BA output with `M`-dotted edges was not written (optional; dispatcher answer (7)).
- O3. `BAAtomInst2.baPQ.g.auxOrd = 2` (prove report) is not reducible by `decide` here (`auxOrd : ℤ`, stuck match); it is not needed by any instance.
No dispatcher sign-off needed. Merge needs: the import line in `RBM3D.lean` and the full `lake build` on current `main` (hub).
