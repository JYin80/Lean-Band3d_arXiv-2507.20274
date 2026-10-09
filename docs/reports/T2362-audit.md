Auditor model: claude-opus-5-5

# T2362 audit (round 1): BA-K00, `BAMLoop` in place (F1) and the `Θ_BA` calculus

Audit time (`date -u`): Fri Oct  9 21:29:55 UTC 2026. Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2362-audit1`, detached at `708bbd4` (= `t/T2362`).
Overall verdict: **PASS** (all targets). No dispatcher sign-off needed.

## 1. Scope of the diff and FlowPins hunks (Target 1)

```
$ git diff main...t/T2362 --name-only
RBM3D/BA/FlowPins.lean
RBM3D/BA/KBase.lean
$ git diff -U0 main...t/T2362 -- RBM3D/BA/FlowPins.lean | awk '/^@@/{print}'
@@ -272,2 +272,2 @@ variable (d L W : ℕ) [NeZero L]
@@ -276 +276 @@ def BAMLoop (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (I : LoopIdx (Zd d L)) :
$ diff <(git show main:RBM3D/BA/FlowPins.lean | sed -n 274,275p) <(git show t/T2362:RBM3D/BA/FlowPins.lean | sed -n 274,275p) && echo IDENTICAL
IDENTICAL
$ diff <(probe t/T2360 T2360Pins.lean:170, BAMLoop' body) <(t/T2362 FlowPins.lean:276) && echo IDENTICAL
IDENTICAL (probe BAMLoop' body line = branch FlowPins:276)
```
Only the docstring (272–273) and body line (276) change; the signature line 274 and the `W^{-(n-1)d}` factor (275) are byte-identical to main. New body = `(I.σ.zip ((I.a.rotate (I.length - 1)).zip I.a)).map (M p.1 p.2.1 p.2.2)`, i.e. `σ_i` on `(a_{i-1}, a_i)`, cyclic, which is `(eq:KMloop)` (`1_2:1003`, `tr ∏ M(σ_i)E_{a_i}`) and `A:571` (edge `b_{j-1}→b_j` carries `σ_j`, `a_j = b_j`), as `loopM` (`Loop/GLoopFlow.lean:92`). The docstring states this convention with `(eq:KMloop)`, `A:571`, `loopM`. Users of `BAMLoop` on main: only `BAKsol` (`FlowPins.lean:283,286`, by name; no proved statement unfolds the body); full build below re-checks `BA/Step1Fam`.
**Target 1: PASS.**

## 2. Statements against the ticket (Target 2)

Statements read from `t/T2362:RBM3D/BA/KBase.lean` (the prove report's extract matches the file):

| target | Lean statement (hypotheses → conclusion) | ticket pin | result |
|---|---|---|---|
| `BAMLoop_apply` (54) | `1 ≤ n`, `I.σ.length = n`, `I.a.length = n` → `BAMLoop = (W^d)⁻¹^(n-1) * ∏_{i<n} M(σ.getD i)(a.getD ((i+(n-1))%n))(a.getD i)` | index form, `a_{-1}=a_{n-1}`, `getD` allowed | match |
| `BAMLoop_le_two` (81) | `∀ σ, (M σ)ᵀ = M σ`, `I.length ≤ 2` → `BAMLoop = old body` (verbatim main body, `I.a.zip (I.a.rotate 1)`) | `n ≤ 2`, symmetric `M σ` | match (no σ-length hyp: more general) |
| `BAMLoop_witness` (108) | `BAMLoop 1 3 1 BAMLoop_witM ⟨[true,true,false],[![0],![1],![2]]⟩ = 15` | value 15 at that data | match; `BAMLoop_witness_old` (121) = 14 for the old body |
| `BATheta_isUnit` (324) | `BAReal d L g κ E m`, `0 ≤ t`, `t < 1`, all `σ₁ σ₂` → `IsUnit (1 - (t:ℂ) • BAMss … σ₁ σ₂)` | invertibility | match |
| `BATheta_resolvent` (330) | same hyps → `Θ = 1 + t•(Q*Θ) ∧ Θ = 1 + t•(Θ*Q)` | `Θ = 1+tMΘ = 1+tΘM` | match |
| `BATheta_hasDerivAt` (341) | same hyps, all `a b` → `HasDerivAt (s ↦ Θ_s a b) ((Θ_t*Q*Θ_t) a b) t` | entrywise `∂_tΘ = ΘMΘ` | match (two-sided derivative in `ℝ`) |
| `BATheta_swap` (350) | no hypothesis → `Θ^{σ₁σ₂} = Θ^{σ₂σ₁}` | probe 387 | match (identical to probe statement) |
| `BATheta_conj` (362) | same hyps, all `a b` → `Θ^{(false,false)}_ab = conj Θ^{(true,true)}_ab` | `Θ^{(-,-)} = conj Θ^{(+,+)}` | match (`BAMsigma true = M`, `false = Mᴴ`) |
| `BATheta_isSymm` (371) | same hyps → `Θᵀ = Θ` | `Θᵀ = Θ` | match |
| `BATheta_row_sum_pm` (381) | same hyps, all `a` → `∑_b Θ^{(true,false)}_ab = (1 - t)⁻¹` | rows of `Θ^{(+,-)}` = `(1-t)⁻¹` | match |
| `BAMLoop_trace` (434, recommended) | `[NeZero W]`, `1 ≤ n`, `σ a : Fin n → _` → `BAMLoop (loopOf σ a) = tr (List.ofFn (M(σ i) ⊗ₖ 1_{W^d}) * Eblk (a i)).prod` | trace form in `loopM`'s `List.ofFn` order | delivered (97 lines ≤ 100) |

Definitions used (merged, by grep): `BATheta = PropThetaQ (BAMss …) t = Ring.inverse (1 - (t:ℂ)•Q)` (`MFixedPoint.lean:515`, `Propagator/Pins.lean:214-216`); `BAMss_ab = BAMsigma σ₁ b a * BAMsigma σ₂ a b` = `(eq:Msig)` (`1_2:1070`); `BAReal = BASelf ∧ κ ≤ Im m` (`MFixedPoint.lean:432`). Hypotheses are exactly `BAReal`, `0 ≤ t`, `t < 1`; no hypothesis beyond the ticket's list; `3 ≤ L` not needed (allowed: "where needed"). Quantifiers: every target quantifies all charge pairs / entries as pinned; `BATheta_conj` is the pinned `(-,-)` vs `(+,+)` case.

## 3. Hidden hypotheses, vacuity, cycles

- No new structure or class; no hypothesis sits in a structure field. Calculus inputs are merged theorems: `BAK_row_sum` (`KKernel.lean:124`, needs `BASelf`), `BAMss_norm_eq_BAK` (`:102`), `BAMss_pm_eq` (`:84`), `BAMB_symm`. Imports: `RBM3D.BA.FlowPins`, `RBM3D.BA.KKernel`, `RBM3D.Propagator.Deriv` (no `RBM3D` root): no cycle.
- No external hypothesis (all targets deterministic), so no limit check is required.
- Non-vacuity of `BAReal`: instantiated by the merged `P.real` (`MFixedPoint.lean:883,893`; `P : FlowPt 4 10` built from `exists_flowPt`, a theorem, with `0 < Im m₀` inside `BASelf`).
- `t < 1` is sharp, not an artificial restriction: scratch lemma (not committed) re-checked in the audit worktree:
```
$ lake env lean $S/neg.lean   # theorem BAKBase_neg_t_one … (h : BASelf …) : ¬ IsUnit (1 - ((1:ℝ):ℂ) • BAMss … true false)
exit 0
```

## 4. Compiled nonempty instances (`KBase.lean` §4, lines 503–566)

| target | instance data | hypotheses discharged |
|---|---|---|
| `BAMLoop_apply` | `d=1, L=3, W=1`, `n=3`, σ=`(+,+,-)`, labels `(0,1,2)` | `by norm_num`, `rfl`, `rfl` |
| `BAMLoop_le_two` | same `M`, `n=2`, σ=`(+,-)`, labels `(0,2)` (distinct) | `witM_symm` (proved), `by decide` |
| `BAMLoop_witness` | is itself a closed statement at concrete data (15) | none |
| `BAMLoop_trace` | `W=2` (`W^d=2`), `n=3`, same loop | `by norm_num` |
| `BATheta_isUnit` | `P` (`d=3, L=4`), `t=1/2`, `(+,-)` and `(-,-)` | `P.real`, `by norm_num` ×2 |
| `BATheta_resolvent` / `_isSymm` | `P`, `t=1/2`, `(+,+)` | `P.real`, `by norm_num` ×2 |
| `BATheta_hasDerivAt` | `P`, `t=1/2`, `(+,-)`, entry `(0, (1,0,0))` | `P.real`, `by norm_num` ×2 |
| `BATheta_swap` | `P`, `t=1/2`, `(+,-)` | none needed |
| `BATheta_conj` | `P`, `t=1/2`, entry `(0, (1,0,0))` | `P.real`, `by norm_num` ×2 |
| `BATheta_row_sum_pm` | `P`, `t=1/2`, row `0` (value `2`) | `P.real`, `by norm_num` ×2 |

No `N = 0`, empty index, collapsed window or `False` premise; `L = 3, 4`, `t = 1/2` interior. Audit addition (compiled): the witness separates the two pairings.
```
example : BAMLoop 1 3 1 BAMLoop_witM ⟨[true, true, false], [![0], ![1], ![2]]⟩ ≠ 14 := by
  rw [BAMLoop_witness]; norm_num          -- in $S/audit_axioms.lean, exit 0 below
```

## 5. Build, axioms, hygiene (audit worktree)

```
$ lake build RBM3D.BA.FlowPins RBM3D.BA.KBase
✔ [3739/3739] Built RBM3D.BA.KBase (3.6s)
Build completed successfully (3739 jobs).
grep -c '^error' → 0
$ lake build            # full library (re-checks every importer of FlowPins)
✔ [4170/4173] Built RBM3D.BA.Step1Fam (12s)
Build completed successfully (4173 jobs).
grep -c '^error' → 0
$ lake env lean $S/audit_axioms.lean; echo "exit $?"
'RBM.BA.BAMLoop' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMLoop_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMLoop_le_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMLoop_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMLoop_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BATheta_isUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BATheta_resolvent' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BATheta_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BATheta_swap' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BATheta_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BATheta_isSymm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BATheta_row_sum_pm' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
$ git show t/T2362:RBM3D/BA/KBase.lean | grep -nE '\bsorry\b|\badmit\b|native_decide|^axiom'; echo "grep exit $?"
grep exit 1
$ git show t/T2362:RBM3D/BA/KBase.lean | grep -cE '^private (theorem|def|lemma)'   # and those without BAKBase_
20
0
```
`wc -l KBase.lean` = 569 (< stop line 950). `Test/Axioms.lean` untouched (not in the diff). Frozen signatures: only `BAMLoop`'s body changed, as the ticket authorises (supervisor 2051 Q2, in place).

## 6. Paper deltas

- F1 (the carrier pairing) is D632 = T2360a in `docs/paper-deltas.md:1591`: covered.
- `t ∈ [0,1)` in Lean vs `t ∈ [0,1]` in `def_Theta` (`1_2:1072`): proposed by the prover as candidate **T2362a** (prove report §(d)), with the compiled non-invertibility at `t = 1`: covered.
- `BATheta_swap` is a lemma, not a delta (T2360c, not numbered per supervisor 2051 O6). No other Lean/paper statement difference found.

## 7. Observations (no effect on statement, instance, build, axioms or delta coverage)

- O1. `BAMLoop_witness_old` and `KBaseInst.witM_symm` are public, unpinned names; `BAMLoop_witness_old` is not file-stem-prefixed (§3 (E)). Name grep on main finds no clash. Suggested only.
- O2. `ht0 : 0 ≤ t` and `κ` in `BAReal` are unused by the proofs (the prover says only `BASelf` and `|t| < 1` are used). The ticket pins them, so this is not a defect.

## Verdict per target

| target | verdict |
|---|---|
| 1 `BAMLoop` in place (FlowPins 272–276) | PASS |
| `BAMLoop_apply`, `BAMLoop_le_two`, `BAMLoop_witness` | PASS |
| `BATheta_isUnit`, `_resolvent`, `_hasDerivAt`, `_swap`, `_conj`, `_isSymm`, `_row_sum_pm` | PASS |
| `BAMLoop_trace` (recommended) | PASS |

`$S` = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/966b45d4-be15-4db2-88b3-45a074bfecd5/scratchpad/T2362`.
