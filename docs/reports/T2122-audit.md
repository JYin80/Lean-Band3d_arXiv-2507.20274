Auditor model: claude-opus-5-5
# T2122 audit (round 1): KL12 `Loop/KLWardIneq`, `lem_wardineq_K`

Written Sun Oct  4 08:03:39 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2122-audit1`, detached at `t/T2122` = `d2a52e9`.

## 1. Diff scope and hygiene
```
$ git diff --name-only main...HEAD
RBM3D/Loop/KLWardIneq.lean
$ grep -nE "sorry|admit|native_decide|^axiom|^open private|set_option" RBM3D/Loop/KLWardIneq.lean
79:set_option linter.style.longLine false
81:open private sigmaIn sigmaOut from RBM3D.Loop.KLSumZeroWard
$ grep -cE "^private " RBM3D/Loop/KLWardIneq.lean
15
```
Only the sole writable file; `Test/Axioms.lean` untouched (the ticket expects no new line). The only `open private` is the one the ticket allows. Imports: `Batteries.Tactic.OpenPrivate`, `RBM3D.Loop.KLInduct` (not `RBM3D`). No merged file is changed, so no frozen signature is touched.

## 2. Target 1: the pins, verbatim (script diff against the check file)
```
$ awk '<def KLwardIneqAt .. KLwardIneqAt d n κ gmax>' docs/tickets/checks/T2122-check.lean > pin_check.txt
$ awk '<same>' RBM3D/Loop/KLWardIneq.lean > pin_file.txt
$ wc -l pin_check.txt pin_file.txt; diff pin_check.txt pin_file.txt && echo PIN-IDENTICAL
      10 pin_check.txt
      10 pin_file.txt
PIN-IDENTICAL
```
Against the paper (`3_5_Loop_Hierarchy.tex:1001-1005`: "For any `n ≥ 2` and `t ∈ [0,1)`, `max_σ Σ_{a_n} |𝒦^{(n)}_{t,σ,a}| ≺ (W^dη_t)⁻¹(W^{-d}B_{t,0})^{n-2}`"): `2 ≤ n`; `σ : Fin n → Bool` universally quantified (= `max_σ`); the summed label is the last one (`List.ofFn a ++ [x]`); `t ∈ [0,1)` via `KLPar.ht0/ht1`; `∃ C` before `∀ p σ a`, so `C = C(d,n,κ,gmax,τ)` (never `L,W,g,t,E`); `≺` read as `C L^τ` (existing delta D178/T2004e; the `N`-scale is D55/T2041h). Dimension `3 ≤ d`, window `|E| ≤ 2-κ`, `0 < g ≤ gmax` are the `KLPar` fields of the merged layer. Statement: **PASS**.

## 3. Targets 2 and 3: statements (extracted from the file)
```
L956 theorem KLwardIneqPin_holds : KLwardIneqPin
L663 def KLWardIneq_KpiAt (d m : ℕ) (κ gmax : ℝ) : Prop :=
    ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin (m + 1) → Bool)
    (π : Finset (Fin (m + 1) × Fin (m + 1))) (a : Fin (m + 1) → Zd d p.L),
    ∑ x : Zd d p.L, ‖KLKpi d p.L p.g (mSigma p.E) p.t σ (Function.update a (Fin.last m) x) π‖
    ≤ C * (p.L : ℝ) ^ τ * (Gauss.etaT p.E p.t)⁻¹ * (Bparam d p.L p.g p.t 0) ^ (m - 1)
L852 theorem KLWardIneq_KpiAt_holds (d m : ℕ) (κ gmax : ℝ) (hd : 3 ≤ d) (hm : 2 ≤ m) (hκ : 0 < κ)
    (hg : 0 < gmax) (hPT : KLPT d κ gmax) : KLWardIneq_KpiAt d m κ gmax
L676 theorem KLWardIneq_Kpi_step ... (hPT : KLPT d κ gmax)
    (hout : ∀ m'' : ℕ, 2 ≤ m'' → m'' < m → KLWardIneq_KpiAt d m'' κ gmax) : KLWardIneq_KpiAt d m κ gmax
L431 theorem KLWardIneq_Kpi_empty_bound ... (hPT : KLPT d κ gmax) (τ : ℝ) (hτ : 0 < τ) : ∃ C ... (layer ∅)
L864 theorem KLWardIneq_At_two (d : ℕ) {κ gmax : ℝ} (hκ : 0 < κ) : KLwardIneqAt d 2 κ gmax
L899 theorem KLWardIneq_At_of_Kpi (d m : ℕ) (κ gmax : ℝ) (hd : 3 ≤ d) (hm : 2 ≤ m) (hκ : 0 < κ)
    (hg : 0 < gmax) (hPT : KLPT d κ gmax) : KLwardIneqAt d (m + 1) κ gmax
```
Target 2 (`(eq:K-pi-bound_partial)`, `A_deterministic_estimates.tex:812-814`): `n = m+1`, exponent `B^{m-1} = B^{n-2}`, `η_t⁻¹` once, every `π`, every `σ`, summed last label, `∃ C` before `∀ p σ π a`. Range `n ≥ 3` instead of the ticket's `n ≥ 2`: `KLKpi` enters `KLK` only through `KLK_eq_sum_Kpi`, which needs `3 ≤ n` (signature below; `KLgen` uses `kTwo` at length 2), the merged KL11 pin `KLKpiBoundAt` is also `3 ≤ n`, and the `n = 2` content of the lemma is delivered at pin level by `KLWardIneq_At_two` (every `σ`, including `(s,s)`). Proposed as delta `T2122c`. Not a weakening of any endpoint; recorded as an observation.
```
$ grep -n "theorem KLK_eq_sum_Kpi" -A 1 RBM3D/Loop/KLTree.lean
392:theorem KLK_eq_sum_Kpi (W : ℕ) (E t : ℝ) {n : ℕ} [NeZero n] (hn : 3 ≤ n)
393-    (σ : Fin n → Bool) (a : Fin n → Zd d L) :
```
Target 3: `KLwardIneqPin_holds : KLwardIneqPin`, no extra hypotheses (the pin's only hypothesis is `KLPT d κ gmax`). Statements: **PASS**.

## 4. Vacuity, hidden hypotheses, cycles
- No new `structure`. `KLPar` (`KLTree.lean:250`) fields are parameter constraints `3 ≤ L, 1 ≤ W, 0 < g ≤ gmax, |E| ≤ 2-κ, 0 ≤ t < 1`, part of the pin. `KLPT` (`KLTree.lean:321`) is the merged bundle of `lem_propTH` shapes (`KLDecay, KLShort, KLDiffOne, KLDiffTwo, KLZero`), another gate's pin, registered in the axiom registry (below); not introduced here.
- The only new `Prop` `KLWardIneq_KpiAt` is concluded by `KLWardIneq_KpiAt_holds`; `hout` of `KLWardIneq_Kpi_step` is the induction hypothesis, discharged by `KLWardIneq_KpiAt_holds` itself (strong induction, `m'' < m`), no cycle.
- Dependencies are merged (`KLInduct` f4cc46d and its imports). Registry pre-check in the audit worktree:
```
$ printf "import RBM3D\nimport RBM3D.Loop.KLWardIneq\n#assert_rbm_axioms\n" | lake env lean --stdin; echo exit=$?
exit=0
axiom audit: 3830 theorems, 1330 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.Loop.KLPT: 19 [no certificate]
premises found by scanning: 79 (borrowed 2, owed 62, structural 15).
```
(The prover's counts, 3677/80, were taken against an older `main` build cache; the scan adds no new owed premise. Observation only.) External hypothesis `KLPT`: limit check by `T2115/pre2.py` pasted in the prove report (a) (`(1-t)rowsum=1.000000` at `1-t ∈ {1e-1,1e-6,1e-9}`, `KLZero/KLDecay/KLShort` ratios bounded); it is not new in this ticket. **PASS**.

## 5. Compiled nonempty instances (`RBM3D/Loop/KLWardIneq.lean:965-1082`)
```
$ grep -n "^example" RBM3D/Loop/KLWardIneq.lean
977:example (hPT : KLPT 3 1 1) :
1009:example (hPT : KLPT 3 1 1) :
1041:example (hPT : KLPT 3 1 1) :
1052:example (hPT : KLPT 3 1 1) :
1063:example (hPT : KLPT 3 1 1) : KLwardIneqAt 3 3 1 1 ∧ KLwardIneqAt 3 4 1 1 :=
1069:example :
1078:example (hPT : KLPT 3 1 1) : KLwardIneqAt 3 3 1 1 ∧ KLwardIneqAt 3 4 1 1 :=
$ sed -n 857,874p RBM3D/Loop/KLTree.lean | grep -E "L :=|W :=|g :=|def KLinst"; grep -n "def KLInduct_inst" RBM3D/Loop/KLInduct.lean
noncomputable def KLinstPar : KLPar 1 1 where
  L := 5
  W := 2
  g := 1 / 2
def KLinstσ : Fin 3 → Bool := ![true, false, true]
def KLinsta : Fin 3 → Zd 3 5 := ![0, 1, 2]
1212:def KLInduct_instσ : Fin 4 → Bool := ![true, true, false, false]
1215:def KLInduct_insta : Fin 4 → Zd 3 5 := ![![0, 0, 0], ![1, 0, 0], ![0, 1, 2], ![2, 2, 2]]
```
- `KLwardIneqPin_holds` (target 3): line 977 applies it at `d = 3`, `n = 2, 3, 4`, `τ = 1`, `p = KLinstPar` (`L = 5, W = 2, g = 1/2, E = 0, t = 9/10`, the ticket's data; the statement elaborates against `KLK 3 5 (1/2) 2 0 (9/10)`), `σ = (+,-)`, `(+,-,+)`, `(+,+,-,-)`, distinct labels; lines 1063 (`KLwardIneqAt 3 3 1 1 ∧ KLwardIneqAt 3 4 1 1`, the ticket's required `n = 3, 4`).
- `KLWardIneq_KpiAt_holds` (target 2): line 1009 at `n = 4` with layers `∅, {(0,2)}, {(1,3)}` and at `n = 3`; `KLWardIneq_Kpi_step` (1041, `hout` discharged by `KLWardIneq_KpiAt_holds`), `KLWardIneq_Kpi_empty_bound` (1052), `KLWardIneq_At_two` (1069, `σ = (+,+)`, no hypothesis left), `KLWardIneq_At_of_Kpi` (1078).
- Every deterministic hypothesis (`3 ≤ d`, `2 ≤ n`, `0 < κ`, `0 < gmax`, `KLPar` fields, `0 < τ`) is discharged; only `KLPT 3 1 1` (another gate's pin, allowed by the ticket) remains. Nondegenerate: `L = 5 ≥ 3`, `t = 9/10 ∈ [0,1)`, `E = 0` inside the window, `η_t = 1/10`, nonempty index sets. **PASS**.

## 6. Build and axioms (audit worktree)
```
$ lake build RBM3D.Loop.KLWardIneq 2>&1 | grep -E "error|warning|Build"
Build completed successfully (3258 jobs).
$ lake env lean ax.lean     # #print axioms of the six public theorems
'RBM.Loop.KLwardIneqPin_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLWardIneq_KpiAt_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLWardIneq_Kpi_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLWardIneq_Kpi_empty_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLWardIneq_At_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLWardIneq_At_of_Kpi' depends on axioms: [propext, Classical.choice, Quot.sound]
```
No error or warning lines. Name clash against `main`:
```
$ for n in <9 public names>; do git grep -nE "(theorem|def) $n\b" main -- RBM3D | wc -l; done
KLwardIneqAt 0 | KLwardIneqPin 0 | KLWardIneq_Kpi_empty_bound 0 | KLWardIneq_KpiAt 0 | KLWardIneq_Kpi_step 0
KLWardIneq_KpiAt_holds 0 | KLWardIneq_At_two 0 | KLWardIneq_At_of_Kpi 0 | KLwardIneqPin_holds 0
```
Unpinned public names carry the stem prefix `KLWardIneq` (rule E). **PASS**.

## 7. Paper-delta coverage
| Lean/paper difference | coverage |
|---|---|
| `≺` read as `C L^τ`, `∃ C` uniform | D178 (T2004e), existing |
| pin on `L`, sequence pin `STKward` on `N` | D55 (T2041h), existing |
| conditional on `KLPT` (`lem_propTH` shapes) | KL-layer convention (D240/T2115c, T2004 pins), existing |
| induction on vertices for standard `K^{(π)}`, not molecules for `K̃^{(π)}` | D238 (T2115a); candidate T2122b |
| `π = ∅`, last leaf short (`σ_n = σ_1`): paper `:816-818` displays only `Θ^{(+,-)}`; proved by absolute values | candidate T2122a (proof gap, statement unchanged) |
| target 2 for `n ≥ 3`; `n = 2` from `KLK_two` | candidate T2122c |
**PASS**.

## 8. Observations (no RETURN)
- The `STKward` bridge is described in the prove report item 6 (needs `KLPT` from KL14, `KLPar` data per `n`, `STKI = KLK`, `Bctl = (W^d)⁻¹Bparam`, an `L^τ → N^τ` lemma; no `L`-version of `Sizes.W_rpow_le` exists). Not a target.
- Four private helpers are copied from merged files (`KLMolecule_sum_slice`, `KLMolecule_sum_exp_maxDist`, `exists_innermost`, `Flong_subset_diagonals`) because the ticket forbids further `open private`; the report suggests KL14 make them public.
- Registry counts in the prove report differ from this run only because `main` advanced; exit 0 in both.

## Verdict
| target | verdict |
|---|---|
| 1 `KLwardIneqAt`, `KLwardIneqPin` (verbatim) | PASS |
| 2 `(eq:K-pi-bound_partial)` = `KLWardIneq_KpiAt_holds` (`n ≥ 3`, T2122c) | PASS |
| 3 `KLwardIneqPin_holds` | PASS |

Overall: **PASS**. No dispatcher sign-off needed.
