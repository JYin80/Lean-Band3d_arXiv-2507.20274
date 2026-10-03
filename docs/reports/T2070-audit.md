Auditor model: claude-opus-5-5
# T2070 audit, round 1 (KL8+9: `KLmolecule_holds`, `KLsumZero_holds`; extra `KLShort_holds`)
Started Sat Oct  3 20:51:07 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2070-audit1`, detached at `t/T2070` = `ffa1a9e`.
Scratch: `scratchpad/T2070/{audcheck,precheck}.lean`.

## 0. Diff against main
```
$ git diff --stat main...t/T2070
 RBM3D/Loop/KLMolecule.lean | 1029 ++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1029 insertions(+)
$ git merge-base main HEAD; git diff --stat bbd22a5 main -- RBM3D | tail -1   (main drift since branch point)
bbd22a5
 8 files changed, 8926 insertions(+)     (7 new modules + 4 lines of Test/Axioms.lean; no file imported by KLMolecule changed)
```
Sole writable files: `RBM3D/Loop/KLMolecule.lean` (new), `RBM3D/Test/Axioms.lean` (untouched). OK.

## 1. Statements against the pins (check file `docs/tickets/checks/T2070-check.lean`)
Script: `audcheck.lean` = `import RBM3D` + `import RBM3D.Loop.KLMolecule` + the check file's namespace `RBM.Loop.T2070Check`
(defs `KLmoleculeAt`, `KLmoleculePin`, `KLsumZeroAt`, `KLsumZeroPin`, copied by `sed` verbatim) + these lines:
```
example : KLmoleculePin := RBM.Loop.KLmolecule_holds
example : KLsumZeroPin := RBM.Loop.KLsumZero_holds
example : KLmoleculePin = (∀ (d n : ℕ) [NeZero n] (κ gmax : ℝ), 3 ≤ d → 3 ≤ n → 0 < κ → 0 < gmax → KLShort d κ gmax → RBM.Loop.KLmoleculeAt d n κ gmax) := rfl
example : KLsumZeroPin = (∀ (d n : ℕ) [NeZero n] (κ gmax : ℝ), 3 ≤ d → 4 ≤ n → Even n → 0 < κ → 0 < gmax → KLShort d κ gmax → RBM.Loop.KLsumZeroAt d n κ gmax) := rfl
example (d n : ℕ) [NeZero n] (κ gmax : ℝ) : KLmoleculeAt d n κ gmax = RBM.Loop.KLmoleculeAt d n κ gmax := rfl
example (d n : ℕ) [NeZero n] (κ gmax : ℝ) : KLsumZeroAt d n κ gmax = RBM.Loop.KLsumZeroAt d n κ gmax := rfl
#check / #print axioms (below)
```
```
$ lake env lean scratchpad/T2070/audcheck.lean; echo "exit: $?"
RBM.Loop.KLmolecule_holds : ∀ (d n : ℕ) [inst : NeZero n] (κ gmax : ℝ),
  3 ≤ d → 3 ≤ n → 0 < κ → 0 < gmax → RBM.Loop.KLShort d κ gmax → RBM.Loop.KLmoleculeAt d n κ gmax
RBM.Loop.KLsumZero_holds : ∀ (d n : ℕ) [inst : NeZero n] (κ gmax : ℝ),
  3 ≤ d → 4 ≤ n → Even n → 0 < κ → 0 < gmax → RBM.Loop.KLShort d κ gmax → RBM.Loop.KLsumZeroAt d n κ gmax
RBM.Loop.KLShort_holds : ∀ (d : ℕ) (κ gmax : ℝ), 3 ≤ d → 0 < κ → 0 < gmax → RBM.Loop.KLShort d κ gmax
'RBM.Loop.KLmolecule_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLsumZero_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLShort_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLMolecule_inst_molecule' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLMolecule_inst_sumZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLMolecule_inst_signed_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLMolecule_inst_molecule_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
exit: 0
```
Both theorem statements are definitionally (`rfl`) the pin bodies; the file's `KLmoleculeAt`/`KLsumZeroAt` are `rfl`-equal
to the check file's. Against the paper (`A_deterministic_estimates.tex:690-692`, `:729-731`): `(eq:molecule-decay)`
"`|Σ^{(∅)}(t,σ,b)| ≤ C exp(-c max|b_i-b_j|)` for some constants" -- Lean: `∃ C c` before `∀ p σ δ` (constants uniform in
`L, W, g, E, t, σ`, dependence on `d, n, κ, gmax` only). `(eq:Sigma-empty-sum-zero)`: sum over `b \ {b_1}` (Lean: slice
`δ 0 = x`), `OO(|1-t|)` and `OO(λ² + |1-t|)` (Lean: `C(1-t)`, `C(g²+(1-t))`, `t<1` from `KLPar.ht1`), `σ` alternating
(Lean: `KLsigAlt n`, `n ≥ 4` even, as pinned). Quantifier order and losses as pinned.

## 2. Hidden hypotheses, vacuity, cycles
```
$ grep -n "^structure KLPar" -A12 RBM3D/Loop/KLTree.lean   (domain of p; fields are the parameter ranges of the pin)
250:structure KLPar (κ gmax : ℝ) where   L, W : ℕ, hL : 3 ≤ L, hW : 1 ≤ W, g, hg0 : 0 < g, hg1 : g ≤ gmax,
     E, hE : |E| ≤ 2 - κ, t, ht0 : 0 ≤ t, ht1 : t < 1        (condensed; no other field)
$ grep -n "^def KLShort" -A6 RBM3D/Loop/KLTree.lean
278:def KLShort (d : ℕ) (κ gmax : ℝ) : Prop :=
  ∃ Cκ > (0 : ℝ), ∃ cκ > (0 : ℝ), ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ gmax →
    ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s : Bool, ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ a : Zd d L,
      ‖Theta d L g ((t : ℂ) * (mSigma E s * mSigma E s)) 0 a‖ ≤ Cκ * ((if a = 0 then 1 else 0) + g ^ 2 * Real.exp (-cκ * (zdistD d L a : ℝ)))
$ grep -n "theorem prop5Short_holds" RBM3D/Propagator/Prop5Short.lean; sed -n 47,49p RBM3D/Propagator/Pins.lean
400:theorem prop5Short_holds (d : ℕ) (Λ κ : ℝ) : Prop5Short d Λ κ := by
def Prop5Short (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
```
- `KLShort` (the only non-arithmetic hypothesis of both pins) is discharged by `KLShort_holds` (merged, unconditional
  `prop5Short_holds` at `κ'' = √(κ(4-κ))/2 ≤ Im m(E)`; `κ > 2` branch: `|E| ≤ 2-κ < 0` impossible, vacuous as stated).
  Hence the pins hold with no external hypothesis; no TEAM §8 lesson 14 limit check is owed. `KLShort_holds`'s own
  instance: `example : KLShort 3 (1 / 2) 2 := KLShort_holds 3 (1 / 2) 2 ...` (file line 1013), compiled.
- Dependencies: `KLMolecule` imports `Loop.KLSumZeroWard`, `Loop.PureLoop`, `Propagator.Prop5Short`, all merged
  (`RBM3D.lean:92, 23, 49`); no reverse import (`grep -rn KLMolecule RBM3D --include=*.lean` outside the file: 0 hits per report; new file is a leaf).
- Registry pre-check (DECISIONS §16, §20):
```
$ printf 'import RBM3D\nimport RBM3D.Loop.KLMolecule\n#assert_rbm_axioms\n' > precheck.lean; lake env lean precheck.lean; echo exit
exit: 0
1:axiom audit: 2534 theorems, 1066 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
98:premises found by scanning: 82 (borrowed 2, owed 66, structural 14).
```
(counts differ from the prove report's 2291/79 because this worktree's `.lake/build` is a copy of main's newer build; exit 0 is what matters.)

## 3. Compiled nonempty instances
`KLinstPar : KLPar 1 1` (merged `KLTree.lean:857`): `L = 5, W = 2, g = 1/2, E = 0, t = 9/10`; `KLinstσ = ![true,false,true]`, `KLinsta = ![0,1,2]`.
```
930: theorem KLMolecule_inst_molecule : ∃ C, 0 < C ∧ ∃ c, 0 < c ∧
       ‖KLSigmaPi 3 5 (1/2) (mSigma 0) (9/10) KLinstσ ∅ KLinsta‖ ≤ C * Real.exp (-(c * KLmaxDist 3 5 KLinsta)) ∧
       ‖KLSigmaPi … KLinstσ ∅ (fun _ => 0)‖ = 1 ∧ ‖…(fun _ => 0)‖ ≤ C * Real.exp (…)          (condensed)
     obtain ⟨C, hC, c, hc, h⟩ := KLmolecule_holds 3 3 1 1 (by norm_num) (by norm_num) one_pos one_pos (KLShort_holds 3 1 1 (by norm_num) one_pos one_pos)
959: theorem KLMolecule_inst_sumZero : ∃ C, 0 < C ∧ ‖∑_{δ 0 = 0} KLSigmaPi 3 5 (1/2) (mSigma 0) (9/10) (KLsigAlt 4) ∅ δ‖ = 1/19 ∧
       (signed ≤ C(1 - 9/10)) ∧ (absolute ≤ C((1/2)^2 + (1 - 9/10)))                                (condensed)
     obtain ⟨C, hC, h⟩ := KLsumZero_holds 3 4 1 1 (by norm_num) (by norm_num) ⟨2, by norm_num⟩ one_pos one_pos (KLShort_holds 3 1 1 …)
993-1027: examples: boundary `KLPar 1 1` point L=3, W=1, g=gmax=1, E=1=2-κ, t=99/100, n=6 (both theorems);
          KLmoleculeAt 3 4 1 1; KLmoleculeAt 3 5 (1/2) 2; KLsumZeroAt 3 8 (1/2) 2
```
Every hypothesis discharged (no hypothesis left in the instances, `KLShort` from `KLShort_holds`); data nondegenerate:
`d = 3`, `L = 5` (125 sites), `0 < g < 1`, `t ∈ (0,1)`, three distinct labels; the conclusion is non-trivial
(`‖Σ‖ = 1` at the constant pattern, signed sum `= 1/19 ≠ 0`, proved via merged `SumZero_sum_slice_alt`). Compiled in the build below.

## 4. Build, hygiene, axioms
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2070-audit1 && lake build RBM3D.Loop.KLMolecule 2>&1 | grep -v "^✔" | tail -2
Build completed successfully (3253 jobs).
$ grep -rn "sorry\|admit\|native_decide\|^axiom\|^\s*axiom " RBM3D/Loop/KLMolecule.lean; echo "grep exit $?"
grep exit 1
$ grep -c "^private" RBM3D/Loop/KLMolecule.lean; grep -n "^private" … | grep -vc "KLMolecule_"
31
0
$ for n in <9 public names>; do git grep -nw $n main -- RBM3D RBM3D.lean | wc -l; done
KLmoleculeAt=0 KLsumZeroAt=0 KLShort_holds=0 KLmolecule_holds=0 KLsumZero_holds=0 KLMolecule_inst_molecule_norm=0 KLMolecule_inst_molecule=0 KLMolecule_inst_signed_val=0 KLMolecule_inst_sumZero=0
```
Axioms: section 1 (`[propext, Classical.choice, Quot.sound]` for all targets and instances). No frozen signature touched
(the diff adds one new file only). Public unpinned names `KLShort_holds` (ticket-sanctioned) and `KLMolecule_inst_*` (file-stem prefixed): §3 (E) OK.

## 5. Paper deltas
Lean/paper differences and coverage (report section (d)):
- absolute estimate proved internally for `d ≥ 3` (paper cites [RBSO1D] Claim 4.30), explicit `C(d,n,κ,gmax)`: candidate `T2070a`. Covered.
- explicit constants/rate `c = c_κ/2`, domain `|E| ≤ 2-κ`, `g ≤ gmax`, deterministic `∃ C c` uniform over `KLPar`: candidate `T2070b`. Covered.
- K-loop model restricted to the band/`Theta` propagator (no `M`-edges of the block Anderson model), `n ≥ 4` even for the
  sum-zero pin, layer `π = ∅`: inherited from the T2004 probe pins (as pinned); not new to this ticket.

## Verdicts
| target | statement | hidden hyp / vacuity / cycle | instance | build + axioms | paper deltas | verdict |
|---|---|---|---|---|---|---|
| `KLmolecule_holds` | `rfl` = `KLmoleculePin` | none (`KLShort` discharged by `KLShort_holds`) | `KLMolecule_inst_molecule` + 3 examples | pass, 3 std axioms | `T2070b` | **PASS** |
| `KLsumZero_holds` | `rfl` = `KLsumZeroPin` | none | `KLMolecule_inst_sumZero` (signed `= 1/19`) + 2 examples | pass, 3 std axioms | `T2070a`, `T2070b` | **PASS** |
| `KLShort_holds` (extra) | `KLShort d κ gmax` from `3 ≤ d, 0 < κ, 0 < gmax` | none (merged unconditional `prop5Short_holds`) | `example : KLShort 3 (1/2) 2` | pass, 3 std axioms | none needed | **PASS** |

Observations (no RETURN): the branch point is `bbd22a5`, not current main `a262beb`; main's drift adds only new modules and
registry lines, none imported here; the hub's full build at merge settles it. No dispatcher sign-off needed.
Overall: **PASS**. Finished: see `date -u` below.
Finished: Sat Oct  3 20:51:55 UTC 2026
