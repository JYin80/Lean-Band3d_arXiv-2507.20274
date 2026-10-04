Auditor model: claude-opus-5-5

# T2140 audit (round 1): S5-17 `RBM3D/Evolution/CltSwap.lean`, branch `t/T2140` at `4a77a7f`

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2140-audit1` (detached at `4a77a7f`; merge-base with `main` = `7f82dd6` = `main`).

## 1. Statements: RBM2D `c9a24cf` with the ticket's dictionary applied, diffed against RBM3D

Script `stmts.py`: it extracts every `def`/`theorem` header (up to `:=`, before `section Checks`) from both files,
applies the ticket dictionary (`Coord L W↦CoordF d L W`, `Ω L W↦Ω d L W`, `P L W↦PF d L W g`, `X L W↦X d L W [g]`,
`(d : Sizes)↦{d : ℕ} (sz : Sizes d)`, `seqP d/slice d n↦seqP sz/slice sz n`, law `P (d.L n) (d.W n)↦PF d (sz.L n) (sz.W n) (sz.lam n)`)
to the RBM2D text, and compares the strings.
```
$ git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Evolution/CltSwap.lean > src2d.lean   # 385 lines
$ python3 stmts.py src2d.lean RBM3D/Evolution/CltSwap.lean
RBM2D decls: 20 RBM3D decls: 20
SAME   cltSplit
SAME   MeasurePreservingCltSplit
SAME   cltHybSet
SAME   cltHyb
SAME   CltTelescope
SAME   cltHyb_zero
SAME   cltHyb_card
SAME   cltTelescope
SAME   cltHyb_succ
SAME   cltHyb_eq_update_succ
SAME   cltSwap
SAME   MeasurePreservingCltSwap
SAME   IntegralEqZeroOfCltSwapNeg
SAME   cltHyb_cltSwap
SAME   cltHyb_succ_cltSwap
SAME   update_cltSwap_fst
SAME   measurePreserving_cltSplit
SAME   measurePreserving_cltSwap
SAME   integral_eq_zero_of_cltSwap_neg
SAME   cltTransfer
```
All 20 public declarations named by the ticket are there, and each matches RBM2D exactly under the dictionary. No extra public declaration.
The four private helpers carry the prefix `cltSwap_`, as §3(E) and the ticket require.

Elaborated signatures of the endpoint theorems and the merged law they rely on:
```
measurePreserving_cltSplit : ∀ (d L W : ℕ) (g : ℝ) [NeZero L] [inst : NeZero W], MeasurePreservingCltSplit d L W g
measurePreserving_cltSwap : ∀ (d L W : ℕ) (g : ℝ) [NeZero L] [inst : NeZero W], MeasurePreservingCltSwap d L W g
integral_eq_zero_of_cltSwap_neg : ∀ (d L W : ℕ) (g : ℝ) [NeZero L] [inst : NeZero W], IntegralEqZeroOfCltSwapNeg d L W g
cltTelescope : ∀ (d L W : ℕ) [inst : NeZero L] [inst_1 : NeZero W], CltTelescope d L W
@cltTransfer : ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (f : Ω d (sz.L n) (sz.W n) → ℂ),
  Measurable f →
    ∫ (ω : sz.SeqΩ), f (sz.slice n ω) ∂sz.seqP = ∫ (ω : Ω d (sz.L n) (sz.W n)), f ω ∂PF d (sz.L n) (sz.W n) (sz.lam n)
PF : (d L W : ℕ) → ℝ → [NeZero W] → MeasureTheory.Measure (Ω d L W)
@Sizes.seqP_map_slice : ∀ {d : ℕ} (sz : Sizes d) (n : ℕ),
  MeasureTheory.Measure.map (sz.slice n) sz.seqP = PF d (sz.L n) (sz.W n) (sz.lam n)
```
No hypothesis on `g` and no change of law beyond the dictionary, so the ticket's stop condition does not fire. The law in `cltTransfer` is exactly the
one the merged `seqP_map_slice` provides. The only hypotheses are typeclasses (`NeZero`) and `Measurable f`.

## 2. Vacuity, hidden hypotheses, cycles

- The `Prop` definitions `MeasurePreservingCltSplit/Swap` and `IntegralEqZeroOfCltSwapNeg` are pins. The theorems of the same file *prove*
  them, unconditionally. No structure carrying hypothesis fields is introduced.
- Dependencies: the file imports only `RBM3D.Gauss.FineModel`, which is merged on `main`, plus Mathlib through it. There is no cycle.
- `IntegralEqZeroOfCltSwapNeg` has no integrability hypothesis. This is sound: the proof uses `integral_comp'` along a measurable
  equivalence and `integral_neg`, both valid for every `F`.
- There is no external hypothesis, so no limit check is owed. The registry is unchanged:
```
$ printf 'import RBM3D\nimport RBM3D.Evolution.CltSwap\n#assert_rbm_axioms\n' > reg.lean; lake env lean reg.lean | grep "premises found"
premises found by scanning: 74 (borrowed 0, owed 55, structural 19).
$ printf 'import RBM3D\n#assert_rbm_axioms\n' > reg0.lean; lake env lean reg0.lean | grep "premises found"
premises found by scanning: 74 (borrowed 0, owed 55, structural 19).
(reg.lean: lean exit=0)
```

## 3. Compiled nonempty instances (section `Checks` of the new file, compiled in the module build of §4)

- `measurePreserving_cltSplit`, `measurePreserving_cltSwap` and `integral_eq_zero_of_cltSwap_neg` are each applied at `(d,L,W,g) = (3,3,1,1/2)`.
- `integral_eq_zero_of_cltSwap_neg` is also applied to the concrete antisymmetric `F p = p.1 c - p.2 c`. The swap hypothesis is discharged by `simp [cltSwap]`.
- `cltTelescope` is applied at `(3,3,1)` with the concrete enumeration `Fintype.equivFin (CoordF 3 3 1)`.
- `cltTransfer` is applied at the merged `SizesInst.sz0`, `n = 0`, with `f = ω ↦ (ω c₀ : ℂ)`. Measurability is discharged by
  `Complex.measurable_ofReal.comp (measurable_pi_apply c₀)`.

Every deterministic hypothesis is discharged. The data are nondegenerate: the coordinate set is nonempty, which the auditor checked by compiling the
following (no output, exit 0):
```
example : Fintype.card (CoordF 3 3 1) = 1458 := by simp [CoordF, RBM.Gauss.Idx, RBM.Zd]
def RBM.Gauss.SizesInst.sz0 : Sizes 3 :=
{ L := fun n => 4 * (n + 1), W := fun n => (2 * (n + 1)) ^ 5, lam := fun n => ((2 * (↑n + 1)) ^ 6)⁻¹, ... }
```
At `n = 0`, `sz0` gives `L = 4`, `W = 32`, `lam = 1/64`: not degenerate and not astronomically large.

## 4. Build, axioms, hygiene, scope

```
$ lake build RBM3D.Evolution.CltSwap 2>&1 | grep -i "error\|warning\|sorry\|Build" | tail
Build completed successfully (3244 jobs).
$ lake env lean ax.lean 2>&1 | grep 'depends on axioms' | sed "s/'.*' depends/X depends/" | sort | uniq -c   # all 20 public decls
  20 X depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom|[^#]axiom " RBM3D/Evolution/CltSwap.lean; echo "grep exit=$?"
grep exit=1
$ git diff --name-status main...t/T2140
A	RBM3D/Evolution/CltSwap.lean
$ grep -n "^import" RBM3D/Evolution/CltSwap.lean
6:import RBM3D.Gauss.FineModel
$ for n in <13 public non-helper names>; do git grep -lw "$n" main -- RBM3D | wc -l; done
cltSplit:0 MeasurePreservingCltSplit:0 cltHybSet:0 cltHyb:0 CltTelescope:0 cltSwap:0 MeasurePreservingCltSwap:0 IntegralEqZeroOfCltSwapNeg:0 cltTransfer:0 measurePreserving_cltSplit:0 measurePreserving_cltSwap:0 integral_eq_zero_of_cltSwap_neg:0 cltTelescope:0
```
The diff touches only the sole writable file. `Test/Axioms.lean` is untouched, which is correct because there is no premise. The diff adds a new file, so no frozen signature changes.

## 5. Paper deltas

The Lean statements differ from arXiv:2507.20274 in two ways:
- The i.i.d.-copy and exchange route is not in the paper: `(eq:bound_isolated)` at `3_5:2245` cites [DYYY25] (7.39).
- The telescope runs over the `2(WL)^{2d}` real coordinates, not over entries `i ≤ j`.

Both are proposed in the prove report §(d) as candidate `T2140a`. The candidate is not yet in `docs/paper-deltas.md`
(`grep -n "T2140\|CltSwap" docs/paper-deltas.md` gives no output); the dispatcher appends it. Coverage is complete.

## 6. Observations (no effect on statement, instance, build, axioms or delta coverage)

- O1 (docstrings, target 2): the module docstring is adapted correctly. It cites arXiv:2507.20274, `(eq:bound_isolated)`, `3_5:2245` and [DYYY25] (7.39),
  and it says the copy and the exchange are not in the paper. Several declaration docstrings, however, still carry RBM2D-paper line references that do not exist in
  this paper's TeX:
  - `cltSplit`: "the paper's i.i.d. copy `H'` (7:440–446)";
  - `MeasurePreservingCltSplit`: "`clt-delta` 7:446";
  - `CltTelescope`: "`clt-telescope-general` 7:453";
  - `cltHyb_succ`: "7:446";
  - `MeasurePreservingCltSwap` and `IntegralEqZeroOfCltSwapNeg`: "`clt-ibp` ... 7:602".
  ```
  $ grep -rn "clt-delta\|clt-telescope\|clt-ibp\|clt-lemmatelescope" paper/tex | wc -l
  0
  ```
  By CLAUDE.md §5.7 docstrings are not evidence, and this changes no statement. Suggestion for the dispatcher: a follow-up docstring cleanup that rewrites these references
  as "[DYYY25] Sec. 7 / RBM2D paper" or deletes them.
- O2: the RBM2D check `card_coord_one_one` (`L = W = 1`, two coordinates) was replaced by the applied `cltTelescope` at `(3,3,1)`. This is acceptable: the
  instance is nondegenerate (1458 coordinates, §3).

## Verdict

| target | verdict |
|---|---|
| 1. port of the 20 public declarations (dictionary, no hypothesis on `g`, law of `cltTransfer`) | PASS |
| 2. docstrings (paper id, `(eq:bound_isolated)`, `3_5:2245`, [DYYY25] (7.39), route not in paper) | PASS (observation O1) |
| compiled nonempty instances at `(3,3,1,1/2)` and `sz0`, `n = 0` | PASS |

**T2140: PASS.** No dispatcher sign-off is needed.
