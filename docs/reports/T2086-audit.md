Auditor model: claude-opus-5-5

# T2086 audit (round 1) — S3-03 `Induction/NewPQ`, target `stNewPQ_holds`

Time: Sun Oct  4 00:05:16 UTC 2026 (`date -u`). Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2086-audit1`, detached at `ae37223` (`t/T2086`), merge-base with `main` `3b8c687`.

**Verdict: `stNewPQ_holds` — PASS.**

## 1. Statement against the pin

The target is the merged pin by type ascription (no restatement, so no textual diff is needed); the pin file is untouched on the branch.

```
$ git diff --name-only main...t/T2086
RBM3D/Induction/NewPQ.lean
$ git diff main t/T2086 -- RBM3D/Induction/Step34Pins.lean RBM3D/Test/Axioms.lean | wc -l
       0
$ cat scratchpad/T2086/stmt.lean        # import RBM3D.Induction.NewPQ
#check (stNewPQ_holds : ∀ d, STNewPQ d)
#print axioms stNewPQ_holds
$ lake env lean scratchpad/T2086/stmt.lean; echo exit=$?
stNewPQ_holds : ∀ (d : ℕ), STNewPQ d
'RBM.Gauss.Sizes.stNewPQ_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```

The pin `STNewPQ` (`Step34Pins.lean:330`) compared with `lem: newPQ` (`3_5:1482-1495`):
- Quantifier order: `∀ m σ A, ∃ (ℓ,k,ξ,σ',ι,A')`, then `∀ sz n E τ`, `|E|<2`, `0≤τ<1`, `∀ ω a`. The data are fixed before the sizes, sample and labels, and the **same** data serve `𝓛` and `𝒦` (one `∃`, then the conjunction). This matches the ticket.
- `1 ≤ k_α ≤ m-1` (`k α + 1 ≤ m`), `ξ_α ∈ ℤ`, `I_diff(σ_α) ⊆ A_α`, `A_m = A ∪ I_diff σ`, factor `ξ_α / (2 i N η_τ)^{m-k_α}` with `N = sz.size n = (W L)^d` (`Sizes.lean:157`). These match `(yurenAL)` and `(yurenAK)`.
- Definitions used (by `#print`): `STIdiff σ = {i | σ i ≠ σ (finRotate k i)}` (cyclic). `zeroModeSet A T` is the foldr of `zeroModeOp i f = f − avgOp i f`, with `avgOp i A a = (L^d)⁻¹ Σ_c A (update a i c)`. This is the paper's `Q^{(A)} = Π_{i∈A}(1 − P^{(i)})`.
- No constant depends on `W`, `L`, `λ`, `E`, `τ` or `ω`. `npq_main` (l.479) builds `Ls : List (NPQTerm m)` before `∀ L c T`, and `stNewPQ_holds` (l.584) takes the data from `Ls` before `intro sz n E τ …`.

## 2. Vacuity, hidden hypotheses, cycles

- The only public declaration is `theorem stNewPQ_holds (d : ℕ) : STNewPQ d`. It takes no hypothesis.
- The private `NPQFam`/`NPQWard` (l.257, l.327) are discharged inside the proof: `𝓛` through `npq_loopL_rotate`/`npq_loopL_ward`, and `𝒦` through the merged `KLK_rotate`/`KLK_ward`. They do not occur in the target.
- The pin's hypotheses `|E|<2, 0≤τ<1` are satisfiable (instance below). The identity is not trivially true: with `ℓ = 0` it would say `Q^{(A)} = Q^{(A∪I_diff)}`.
- Dependencies come from imports of merged modules only (the branch changes one new file). There is no cycle: `NewPQ` imports `Step34Pins`, `ConArgDet`, `KLWard`, and nothing imports `NewPQ`.

```
$ lake env lean scratchpad/T2086/audit.lean   (signatures of the merged inputs, abbreviated)
Loop.KLK_rotate : ∀ (d L W) [NeZero L] (g E : ℝ), 3 ≤ L → 1 ≤ W → |E| < 2 → ∀ t ∈ Set.Ico 0 1, ∀ (s b σ a), σ.length = a.length → KLK … {σ := s :: σ, a := b :: a} = KLK … {σ := σ ++ [s], a := a ++ [b]}
Loop.KLK_ward : … 0 ≤ t → t < 1 → … ∑ x, KLK … {σ := s :: μ ++ [!s], a := a ++ [x]} = (2 * I * ↑W ^ d * ↑(etaT E t))⁻¹ * (KLK … {σ := true :: μ, a} - KLK … {σ := false :: μ, a})
sum_gloop_ward_last_div : … IsUnit (H - z • 1) → IsUnit (H - conj z • 1) → z.im ≠ 0 → … ∑ b, loopL … {σ := true :: μ ++ [false], …} = (… - …) / (2 * I * ↑W ^ d * ↑z.im)
```

The `σ₁ = −` order of Ward for `𝓛` and the cyclic rotation of `𝓛` are proved privately here (`npq_loopL_conj`, `npq_loopL_rotate`, `npq_loopL_ward`), as the ticket allows. The step `L^{-d}(2iW^dη)⁻¹ = (2iNη)⁻¹` is `hcL`, proved by `field_simp` with `L, W ≠ 0` and `η > 0`.

## 3. Compiled nonempty instance

`NewPQ.lean:660-678`, an `example` at `d = 3`, `sz0`, `n = 0`, `m = 3`, `σ = (+,−,+)`, `A = ∅`, `E = 0`, `τ = 1/2`, for every `ω` and every `a`. It applies `stNewPQ_holds 3 3 ![true,false,true] ∅`, and `h sz0 0 0 (1/2) (by norm_num) (by norm_num) (by norm_num) ω a` discharges all three deterministic hypotheses. It compiles: the module builds (§4). Nondegeneracy check:

```
$ cat scratchpad/T2086/inst.lean        # import RBM3D.Induction.NewPQ
example : Nonempty sz0.SeqΩ := inferInstance
example : RBM.Gauss.Sizes.STIdiff ![true, false, true] = {0, 1} := by decide
example : sz0.L 0 = 4 ∧ sz0.size 0 = 2097152 := ⟨sz0_values.1, sz0_values.2.2.1⟩
$ lake env lean scratchpad/T2086/inst.lean   (no output, no error)
```

The sample space is nonempty, `I_diff(σ) ≠ ∅` (the expansion is not trivial), `L = 4`, `W = 32`, and `N = 2097152` is not astronomically large. The instance is not degenerate.

## 4. Build, axioms, hygiene

```
$ lake build RBM3D.Induction.NewPQ 2>&1 | grep -v '^✔' | grep -E 'error|warning|Built RBM3D.Induction.NewPQ|Build completed'
warning: RBM3D/Induction/Step34Pins.lean:12:0: The module doc-string for a file should be the first command after the imports.
⚠ [3708/3708] Built RBM3D.Induction.NewPQ (4.2s)
warning: RBM3D/Induction/NewPQ.lean:10:0: The module doc-string for a file should be the first command after the imports.
Build completed successfully (3708 jobs).
$ git show t/T2086:RBM3D/Induction/NewPQ.lean | grep -n -E "\bsorry\b|\badmit\b|^axiom|\baxiom |native_decide|set_option (maxHeartbeats|debug)" || echo none
none
$ git show t/T2086:RBM3D/Induction/NewPQ.lean | grep -n -E "^(theorem|lemma|def|structure|abbrev|instance)"
584:theorem stNewPQ_holds (d : ℕ) : STNewPQ d := by
$ grep -rn 'stNewPQ_holds' RBM3D | grep -v NewPQ.lean || echo "no clash on main"
no clash on main
```

Axioms are exactly `propext, Classical.choice, Quot.sound` (§1). The only warnings are the header-linter style warning, which the merged `Step34Pins.lean` also has. All helpers are `private` (§3 (E)). Frozen signatures are untouched, and the diff is the sole writable file `RBM3D/Induction/NewPQ.lean`. `RBM3D/Test/Axioms.lean` is not touched.

## 5. Paper deltas

The target's type is the merged pin, so this ticket adds no new Lean/paper statement difference. The prove report (d) proposes:
- `T2086a`: the paper's proof `(y2ussz)` treats the deletion of index `i` as if `i < n`. For the cyclic `i = n`, the printed `σ_±` agrees only up to rotation.
- `T2086b`: Lean's `ι_α` are cyclically rotated and not increasing. The pin only uses `a ∘ ι_α`.

Coverage is complete for this ticket.

## Observations (not RETURN)

- O1. The pin does not require `ι α` to be injective, while the paper says `a_α` "consists of a subset of indices in `a`". The Lean construction's `ι` is injective (`npqIota_injective`), but the existential hides this. If S3-20 needs injectivity, it needs a primed pin. The difference is in the pin (T2041/T2049), not in this ticket's target. Dispatcher: consider a paper-delta note against D48–D56.
- O2. The owed registry line `RBM.Gauss.Sizes.STNewPQ` (`RBM3D/Test/Axioms.lean:120`) is not removed. The ticket allows it to go after the merge, and the prove report (d) defers this to a cleanup ticket.
- O3. Proposed candidate `T2086c` (move `npq_loopL_ward`/`npq_loopL_rotate` to public) is a code-organisation note, not a paper delta.

## Verdict

| Target | Verdict |
|---|---|
| `RBM.Gauss.Sizes.stNewPQ_holds : ∀ d, STNewPQ d` | **PASS** |

No dispatcher sign-off is needed.
