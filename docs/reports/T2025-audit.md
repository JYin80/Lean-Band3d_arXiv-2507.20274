Auditor model: claude-opus-5-5

# T2025 audit (round 1): KL4 + KL5, `RBM3D/Loop/KLUnique.lean`
Written Sat Oct  3 05:37 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2025-audit1`, detached at `d1cc86e` (t/T2025).

## 0. Scope of the diff
```
$ git diff --name-status main...t/T2025
A	RBM3D/Loop/KLUnique.lean
$ git diff main...t/T2025 -- RBM3D/Test RBM3D.lean | wc -l
       0
$ git diff --stat $(git merge-base main t/T2025) main -- RBM3D | tail -3   # main drift since base 3dc4f1c
 RBM3D/Propagator/Prop5Hold.lean | 1399 +++
 RBM3D/Propagator/PropUnit.lean  | 1008 +++
```
Only the sole writable file; `Test/Axioms.lean` untouched (KL14's); main drift is in `Propagator/` only (not imported by this module).

## 1. Build and axioms
```
$ lake build RBM3D.Loop.KLUnique 2>&1 | grep -E -i 'error|warning|Build completed|KLUnique'
✔ [3243/3243] Built RBM3D.Loop.KLUnique (8.4s)
Build completed successfully (3243 jobs).
$ lake env lean ax.lean     # import RBM3D.Loop.KLUnique; pin def + `example : KLuniquePin := KLK_unique`; #print axioms; exit=0
'RBM.Loop.KLK_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLK_rotate' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLK_translate' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLretire_twoLoopBounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLretire_kTwoFormula' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLretire_kThree' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLUniqueInst_unique_shifted' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLUniqueInst_rotate_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLUniqueInst_translate_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLUniqueInst_retire_kThree' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -n -E '\b(sorry|admit|native_decide)\b|^\s*axiom\b' RBM3D/Loop/KLUnique.lean; echo "exit=$?"
exit=1
```
Name clashes: each of the 16 public `theorem` names of the file: `git grep -E "(theorem|lemma|def|abbrev) NAME\b" main -- RBM3D` gives 0 hits for all 16. The 21 helpers are `private` with prefix `KLUnique_`.

## 2. Target 1: `KLK_unique` (pin `KLuniquePin`)
Statement: the pin body was copied verbatim from `docs/tickets/checks/T2025-check.lean` into the scratch file above, and
`example : KLuniquePin := KLK_unique` compiles (exit 0): the type is definitionally the pin, which is the same as its syntax (same binders, quantifier order
`d L W [NeZero L] g E`, `3 ≤ L → 1 ≤ W → |E| < 2`, family on `Set.Ico 0 1`, `t ∈ Ico 0 1`, `I.WF`, `1 ≤ I.length`). The file text (lines 117–121) is the pin text.
Dependencies, all merged (signatures printed by `#check` in the same file):
```
@isKLoop_unique : ∀ {d L} [NeZero L] {W} {g}, 3 ≤ L → ∀ (m) {T} {K K'}, IsKLoop d L W g m T K → IsKLoop d L W g m T K' →
  ∀ {T₀ R}, Set.Icc 0 T₀ ⊆ T → 0 ≤ R → (∀ t ∈ Set.Icc 0 T₀, ∀ I, I.WF → I.length = 2 → ‖K t I‖ ≤ R ∧ ‖K' t I‖ ≤ R) →
  ∀ t ∈ Set.Icc 0 T₀, ∀ I, I.WF → 2 ≤ I.length → K t I = K' t I
KLK_isKLoop : ∀ (d L W) [NeZero L] (g E), 3 ≤ L → 1 ≤ W → |E| < 2 → IsKLoop d L W g (mSigma E) (Set.Ico 0 1) fun t I => KLK d L g W E t I
```
The 2-loop bound `R` that `isKLoop_unique` needs is produced inside the proof by `KLretire_twoLoopBounded` (continuity on `[0,t]`), not assumed.
`IsKLoop` (`#print`) is a 3-clause `Prop` (derivative on `T` for length ≥ 2, initial value `MLoop`, length-1 value `m s`): structural, no
extra fields, no bound hidden in it. No cycle: `KLK_unique` ← `isKLoop_unique` (Unique.lean), `KLK_isKLoop` (KLTreeDeriv.lean), `KLretire_twoLoopBounded` (this file).
**Instance.** `KLUniqueInst_unique_one/two/three` (lengths 1, 2, 3 at `d=3, L=5, W=2, g=1/2, E=0, t=9/10`, family `K = KLK`, the trivial case the ticket names)
and `KLUniqueInst_unique_shifted` (family `r J ↦ KLK … r ⟨J.σ, J.a.map (·+e₁)⟩`, i.e. a family that is not `KLK` syntactically, at a length-3 loop with
distinct labels in `Z_5^3`). Every deterministic hypothesis is discharged by `norm_num`/`rfl`/`simp`; the `IsKLoop` premise is the merged
`KLTreeDerivInst_isKLoop : IsKLoop 3 5 2 (1/2) (mSigma 0) (Set.Ico 0 1) fun t I => KLK 3 5 (1/2) 2 0 t I` (`main:RBM3D/Loop/KLTreeDeriv.lean:1080`)
or its shift. Nondegenerate (125 blocks, `W^d = 8`, `t = 0.9`). Compiles (module build above).
**Verdict: PASS.**

## 3. Target 2: retirement lemmas
Text check against the probe (`64b58eb:RBM3D/Probe/T2004Pins.lean:915-971`), blank lines removed:
```
$ diff <(git show 64b58eb:RBM3D/Probe/T2004Pins.lean | sed -n 915,971p | grep -v '^\s*$') <(sed -n 77,111p KLUnique.lean | grep -v '^\s*$')
1d0
< /-! ### Retirement of the old hypotheses (compiled) -/
19,37d17
< /-- **`KLoopBound` is a consequence of the pins `KLBoundAt`** ... -/
< theorem KLretire_KLoopBound {d : ℕ} {κ gmax : ℝ}
<     (hall : ∀ n, 1 ≤ n → KLBoundAt d n κ gmax) (p : KLPar κ gmax) :
...   (19 lines of KLretire_KLoopBound only)
```
The only differences are the probe's section header and `KLretire_KLoopBound`, which the ticket excludes (waits for KL11). `KLretire_twoLoopBounded`,
`KLretire_kTwoFormula`, `KLretire_kThree` (docstrings, statements, proofs) are verbatim. The probe block contains no `KLisKLoopPin`, so nothing to discharge.
`TwoLoopBounded` (merged, `RBM3D/Loop/TreeRep.lean:172`) is `∀ T₀ < 1, ∃ R ≥ 0, ∀ t ∈ [0,T₀], ∀ WF 2-loop I, ‖K t I‖ ≤ R`; the lemma derives it from `IsKLoop` alone
(no new hypothesis `Prop`; DECISIONS §16 respected).
**Instances.** `KLUniqueInst_retire_twoLoopBounded`, `…_kTwoFormula` (with `‖mSigma 0 s‖ = 1` by merged `norm_mSigma`, `(2:ℂ)^3 ≠ 0` by `norm_num`),
`…_kThree` (at `t = 9/10`, charges `(+,-,+)`, labels `0,1,2` in `Z_5^3`), all on `KLTreeDerivInst_isKLoop`. Compiled.
**Verdict: PASS** (all three).

## 4. Target 3: `KLK_rotate`, `KLK_translate` (ports)
RBM2D statements at `c9a24cf` (read-only, `git --no-optional-locks show`):
```
RBM2D/Loop/Cyclic.lean:569 theorem Kcal_rotate :
  ∀ (L W : ℕ) [NeZero L], 3 ≤ L → 1 ≤ W → ∀ E : ℝ, |E| < 2 → ∀ t ∈ Set.Ico (0 : ℝ) 1,
    ∀ (s : Bool) (b : Z2 L) (σ : List Bool) (a : List (Z2 L)), σ.length = a.length →
      Kcal L W E t ⟨s :: σ, b :: a⟩ = Kcal L W E t ⟨σ ++ [s], a ++ [b]⟩
RBM2D/Loop/Cyclic.lean:594 theorem Kcal_translate :
  ∀ (L W : ℕ) [NeZero L], 3 ≤ L → 1 ≤ W → ∀ E : ℝ, |E| < 2 → ∀ t ∈ Set.Ico (0 : ℝ) 1,
    ∀ (c : Z2 L) (I : LoopIdx (Z2 L)), I.WF →
      Kcal L W E t ⟨I.σ, I.a.map (· + c)⟩ = Kcal L W E t I
```
RBM3D (`KLUnique.lean:640`, `:222`):
```
KLK_rotate : ∀ (d L W : ℕ) [NeZero L] (g E : ℝ), 3 ≤ L → 1 ≤ W → |E| < 2 → ∀ t ∈ Set.Ico (0 : ℝ) 1,
  ∀ (s : Bool) (b : Zd d L) (σ : List Bool) (a : List (Zd d L)), σ.length = a.length →
    KLK d L g W E t ⟨s :: σ, b :: a⟩ = KLK d L g W E t ⟨σ ++ [s], a ++ [b]⟩
KLK_translate : ∀ (d L W : ℕ) [NeZero L] (g E : ℝ), 3 ≤ L → 1 ≤ W → |E| < 2 → ∀ t ∈ Set.Ico (0 : ℝ) 1,
  ∀ (c : Zd d L) (I : LoopIdx (Zd d L)), I.WF →
    KLK d L g W E t ⟨I.σ, I.a.map (· + c)⟩ = KLK d L g W E t I
```
Differences: `Z2 L → Zd d L`, `Kcal L W E → KLK d L g W E`, new parameters `d`, `g` (from KL1–KL3's `KLK`), and `E` bound before the hypotheses
instead of after `1 ≤ W` (independent binders; same proposition up to argument order). No hypothesis added or dropped; no `3 ≤ d`.
Hypotheses match those of `KLK_isKLoop`, so they are not vacuous. No cycle: `KLK_translate` uses `KLK_unique` and the private
`KLUnique_isKLoop_shift`; `KLK_rotate` uses the private Grönwall induction `KLUnique_isKLoop_rot`/`KLUnique_rot_eq_on_level` with the bound from
`KLretire_twoLoopBounded`.
**Instances.** `KLUniqueInst_rotate_three` (n = 3), `KLUniqueInst_rotate_four` (n = 4), `KLUniqueInst_translate_three` (n = 3, `c = e₁ = ![1,0,0]`,
labels `![0,0,0], ![1,2,3], ![4,0,1]` in `Z_5^3`), all at `d=3, L=5, W=2, g=1/2, E=0, t=9/10`; every hypothesis discharged; compiled.
**Verdict: PASS** (both).

## 5. Paper deltas
- `t ∈ [0,1)` (all targets) is the accepted delta T2004d (`docs/DECISIONS.md:142`, signed off: `Def_Ktza` `[0,1]` should be `[0,1)`).
- Rotation/translation invariance of `𝒦` is used in the paper but not stated as a lemma: the prove report proposes `T2025a` (note, no
  statement difference). No other Lean/paper statement difference found. Coverage complete.

## 6. Observations (no RETURN)
- O1. The prove report's `(b)` shows a full `lake build` with the root import added locally and removed; the hub repeats this at merge (main has moved
  to include `Propagator/Prop5Hold.lean`, `PropUnit.lean`, unrelated to this module).
- O2. `KLK_rotate`/`KLK_translate` bind `(g E : ℝ)` before the hypotheses (RBM2D binds `E` after `1 ≤ W`): positional callers ported from RBM2D
  must reorder arguments. No mathematical effect.

## Verdict
| target | verdict |
|---|---|
| `KLK_unique` | PASS |
| `KLretire_twoLoopBounded`, `KLretire_kTwoFormula`, `KLretire_kThree` | PASS |
| `KLK_rotate`, `KLK_translate` | PASS |

**T2025: PASS.** No dispatcher sign-off needed.
