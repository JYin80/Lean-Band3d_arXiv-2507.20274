Auditor model: claude-opus-5-5
# T2048 audit (round 1): KL7b, `RBM3D/Loop/KLSumAll.lean`, branch t/T2048 @ 1f823ca

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2048-audit1` (detached at 1f823ca). Started `date -u`: Sat Oct  3 12:54:03 UTC 2026.
Scratch: `scratchpad/A/` (session scratchpad), not committed.

Target: `RBM.Loop.KLK_sumAll_le` (port of RBM2D `Kcal_sumAll_le`, `Loop/SumAll.lean:749` at `c9a24cf`).

## 1. Statement against the pin (ticket: RBM2D statement with `Z2 L -> Zd d L`, `W^2 -> W^d`, `Kcal -> KLK`)
```
$ git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Loop/SumAll.lean > SumAll2D.lean
$ awk '/^theorem Kcal_sumAll_le/,/:= by$/' SumAll2D.lean | sed -e 's/Kcal_sumAll_le/KLK_sumAll_le/' \
    -e 's/Z2 L/Zd d L/g' -e 's/Kcal L W E t (loopOf L σ a)/KLK d L g W E t (KLloopOf d L σ a)/' \
    -e 's/\^ 2 \* etaT/^ d * Gauss.etaT/' > s2.txt
$ awk '/^theorem KLK_sumAll_le/,/:= by$/' RBM3D/Loop/KLSumAll.lean > s3.txt
$ diff s2.txt s3.txt; echo "diff exit $?"
diff exit 0
```
Statement text (RBM3D/Loop/KLSumAll.lean:729; section variables `variable (d : ℕ) (g : ℝ)` at :724, nothing else):
```
theorem KLK_sumAll_le :
  ∀ κ : ℝ, 0 < κ → ∀ (L W : ℕ) [NeZero L], 3 ≤ L → 1 ≤ W → ∀ E : ℝ, |E| ≤ 2 - κ →
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (n : ℕ) (hn : 2 ≤ n) (σ : Fin n → Bool),
      σ ⟨0, by omega⟩ = true → σ ⟨n - 1, by omega⟩ = false → ∀ a₁ : Zd d L,
        ‖∑ a ∈ Finset.univ.filter (fun a : Fin n → Zd d L => a ⟨0, by omega⟩ = a₁),
            KLK d L g W E t (KLloopOf d L σ a)‖
          ≤ 2 ^ (n ^ 2) * (gapK κ)⁻¹ ^ (2 * n) * (((W : ℝ) ^ d * Gauss.etaT E t)⁻¹) ^ (n - 1)
```
- Hypotheses, quantifier order, range `n ≥ 2`, `σ₁ = +`, `σ_n = −`, all `a₁`, constant `2^{n²} c_κ^{-2n}`, exponent `n − 1` on `(W^d η_t)^{-1}`: identical to RBM2D after the ticket's renaming (diff exit 0). `d` free (no `3 ≤ d`), `g` free: no hypothesis added, none dropped. General statement, not a special case.
- Merged objects used in the statement (signatures, `lake env lean ax.lean`):
```
RBM.Loop.KLK : (d L : ℕ) → [NeZero L] → ℝ → ℕ → ℝ → ℝ → RBM.Loop.LoopIdx (RBM.Zd d L) → ℂ
RBM.Loop.KLloopOf : (d L : ℕ) → {n : ℕ} → (Fin n → Bool) → (Fin n → RBM.Zd d L) → RBM.Loop.LoopIdx (RBM.Zd d L)
RBM.Loop.gapK : ℝ → ℝ
RBM.Gauss.etaT : ℝ → ℝ → ℝ
```
- DECISIONS §23 factor `∏ m(σ_i)`: the statement is unchanged by it (norm bound; `‖∏ m‖ = 1`). The prove report's body diff locates it only in the private `KLSumAll_pure_ge3` (`hprodm`), and section (a) row 12 checks it numerically. Consistent with the ticket.

## 2. Hidden hypotheses, vacuity, cycles
```
$ grep -nE "^import|^variable|structure|class |: Prop" RBM3D/Loop/KLSumAll.lean
6:import RBM3D.Loop.KLSumZero
7:import RBM3D.Loop.KLWard
8:import RBM3D.Loop.KLUnique
77:variable {n : ℕ}
111:    (v : Fin n) : Prop :=
242:variable {d L : ℕ} [NeZero L]
421:variable {d L : ℕ} [NeZero L]
635:variable {d L : ℕ} [NeZero L]
724:variable (d : ℕ) (g : ℝ)
$ git -C /Users/junyin/Lean_proof/RBM3D ls-tree --name-only main RBM3D/Loop/KLSumZero.lean RBM3D/Loop/KLWard.lean RBM3D/Loop/KLUnique.lean
RBM3D/Loop/KLSumZero.lean
RBM3D/Loop/KLUnique.lean
RBM3D/Loop/KLWard.lean
```
- No structure/class; the only `Prop` (line 111) is the private combinatorial predicate `KLSumAll_goodPt` (a vertex inside a diagonal's arc), used as a property inside proofs, not as a hypothesis of the target.
- Imports are merged modules on `main`; the file is new, so no cycle. No external hypothesis, so no limit check is needed (TEAM §8 lesson 14).

## 3. Compiled nonempty instances (same file, section 7, lines 754-840)
```
theorem KLSumAll_inst_four (a₁ : Zd 3 3) : ‖∑ a ∈ … (Fin 4 → Zd 3 3) … KLK 3 3 (1/2) 2 0 (1/2) (KLloopOf 3 3 ![true,false,true,false] a)‖ ≤ … :=
  KLK_sumAll_le 3 (1 / 2) 1 one_pos 3 2 (by norm_num) (by norm_num) 0 (by norm_num) (1 / 2)
    ⟨by norm_num, by norm_num⟩ 4 (by norm_num) ![true, false, true, false] rfl rfl a₁
theorem KLSumAll_inst_two  … KLK_sumAll_le 3 (1/2) 1 one_pos 3 2 … 2 (by norm_num) ![true, false] rfl rfl a₁
theorem KLSumAll_inst_three … KLK_sumAll_le 3 (1/2) 1 one_pos 3 2 … 3 (by norm_num) ![true, true, false] rfl rfl a₁
theorem KLSumAll_inst_four_val (a₁ : Zd 3 3) : ‖…n = 4 fibre…‖ ≤ 1024
theorem KLSumAll_inst_two_val (a₁ : Zd 3 3) : ∑ … KLK 3 3 (1/2) 2 0 (1/2) (KLloopOf 3 3 ![true, false] a) = 1 / 4
```
- Data as the ticket requires: `κ = 1`, `d = 3`, `L = 3`, `W = 2`, `g = 1/2`, `E = 0`, `t = 1/2`, `n = 4` with `σ = (+,−,+,−)` and `n = 2` (plus `n = 3`, RBM2D's check). Every hypothesis is discharged by a term (`one_pos`, `norm_num`, `rfl`). None stays open.
- Nondegenerate: `L^d = 27`, the `a₁` fibre is nonempty, and `inst_two_val` proves that the sum equals `1/4 ≠ 0` against the bound `4`. The bound at `n = 4` is `1024` (`inst_four_val`): it is the theorem's own constant, not an inflated witness.
- They compile: the module build in §4 includes section 7.

## 4. Build, axioms, hygiene, diff scope
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2048-audit1 && lake build RBM3D.Loop.KLSumAll 2>&1 | grep -E "error|warning|sorry|Build completed"; echo exit
Build completed successfully (3248 jobs).
exit 0
$ lake env lean scratchpad/A/ax.lean   # collectAxioms over every non-internal decl of the module + #print axioms
module decls (non-internal): 8; non-standard axiom uses: []
'RBM.Loop.KLK_sumAll_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLSumAll_inst_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLSumAll_inst_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLSumAll_inst_two_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLSumAll_inst_three' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
$ grep -nE "sorry|admit|native_decide|^\s*axiom|opaque|implemented_by|extern|set_option" RBM3D/Loop/KLSumAll.lean
67:set_option linter.style.longLine false
$ git -C /Users/junyin/Lean_proof/RBM3D diff --name-status main...t/T2048
A	RBM3D/Loop/KLSumAll.lean
```
- Only the sole writable file `RBM3D/Loop/KLSumAll.lean` is touched. It is new, so no frozen signature changes, and `RBM3D/Test/Axioms.lean` is untouched (no new hypothesis `Prop`, as the ticket expects). The `set_option` at :67 is a style linter only.
- Imports are `KLSumZero`, `KLWard` and `KLUnique`, never `RBM3D`, as pinned. The hub runs the full build and `#assert_rbm_axioms` at merge.

## 5. Paper deltas
- This paper (2507.20274) has no counterpart statement. Its K-loop results are `lem_WI_K` (1_2:1034) and `ML:Kbound` (1_2:1054). The target is a ported auxiliary bound, derived from Ward's identity (`KLK_ward`).
- Design report T2004 row KL7 (`docs/reports/T2004-prove.md:258`) lists the paper delta for this row as "none". The ticket says to cite RBM2D's T2004a-11 (explicit constant) and not re-propose it, and the prove report §(d) does that. The Lean statement does not differ from any statement of this paper, so no new candidate is needed. Coverage is complete.

## Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1. The prove report's (b) list of Mathlib names covers only names that are new relative to RBM2D. That is enough here.
- O2. The ticket asked for an `n = 2` instance "(RBM2D check :775)", but RBM2D's check at :775 is `n = 3`. The file compiles both, so nothing is missing.

## Verdict
`KLK_sumAll_le`: **PASS**
- §1: the statement equals the pinned RBM2D statement after the ticket's renaming (diff exit 0).
- §2: no hidden hypothesis.
- §3: the instances are compiled and nondegenerate.
- §4: the module builds; the axioms are standard; the diff touches only the sole writable file.
- §5: delta coverage is complete.

Ticket T2048: PASS. No dispatcher sign-off needed.
