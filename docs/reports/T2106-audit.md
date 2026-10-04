Auditor model: claude-opus-5-5
# T2106 audit (round 1) — KL10b `RBM3D/Loop/KLIndStepB.lean`
Date (`date -u`): Sun Oct  4 05:40:09 UTC 2026. Audit worktree `RBM3D-wt/T2106-audit1`, detached at `d15d862` (t/T2106). Scratch: `scratchpad/T2106/`.

## 0. Scope and build
```
$ git diff --name-status main...t/T2106
A	RBM3D/Loop/KLIndStepB.lean
$ git log --oneline main..t/T2106
d15d862 T2106: KL10b instance with a spread labelling
79729e3 T2106: KL10b RBM3D/Loop/KLIndStepB.lean (case (ii) of (eq:ind-step-bound), KLindStepPin)
$ git diff main...t/T2106 -- RBM3D/Loop/KLIndStepA.lean RBM3D/Loop/KLMolecule.lean RBM3D/Loop/KLTree.lean RBM3D.lean RBM3D/Test/Axioms.lean | wc -l
       0
$ lake build RBM3D.Loop.KLIndStepB 2>&1 | grep -E "error|warning|sorry|Build|KLIndStepB"
✔ [3256/3256] Built RBM3D.Loop.KLIndStepB (27s)
Build completed successfully (3256 jobs).
$ grep -nE "sorry|admit|native_decide|^axiom|open private" RBM3D/Loop/KLIndStepB.lean
13:`Loop/KLIndStepA.lean` is reused (no `open private` is added).      # docstring only
$ grep -n "^import" RBM3D/Loop/KLIndStepB.lean
6:import RBM3D.Loop.KLIndStepA
```
Only the sole writable file `RBM3D/Loop/KLIndStepB.lean` is touched (new); `Test/Axioms.lean` unchanged (no new hypothesis `Prop`; `KLindStepPin` is proved here). No merged file, no frozen signature touched.

## 1. Axioms (`lake env lean scratchpad/T2106/aud.lean`, imports `RBM3D.Loop.KLIndStepB`)
```
'RBM.Loop.KLindStepAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLindStepPin' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLindStep_alt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLindStepAt_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLindStepPin_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```
The same file also elaborates `example : KLindStepPin := KLindStepPin_holds` (no error).

## 2. Target 1 — `KLindStepAt`, `KLindStepPin` (verbatim pins)
```
$ diff <(awk '/^def KLindStepAt/{p=1} /^end RBM/{p=0} p' docs/tickets/checks/T2106-check.lean | grep -v '^$') \
       <(sed -n 55,66p RBM3D/Loop/KLIndStepB.lean | grep -v '^$'); echo "diff exit=$?"
diff exit=0
$ diff <(git show 64b58eb:RBM3D/Probe/T2004Pins.lean | sed -n 845,863p | awk '/^def KLindStepAt/{p=1} p' | grep -v '^$') \
       <(sed -n 55,66p RBM3D/Loop/KLIndStepB.lean | grep -v '^$'); echo "probe diff exit=$?"
probe diff exit=0
```
Both defs are in `namespace RBM.Loop` (file line 42). Text identical to the check file and the probe pin. **PASS.**

## 3. Target 2 — `KLindStep_alt`
```
@KLindStep_alt : ∀ {d : ℕ} {κ gmax : ℝ} (n : ℕ) [inst : NeZero n],
  3 ≤ d → 3 ≤ n → 0 < κ → 0 < gmax → KLPT d κ gmax →
   ∀ (τ : ℝ), 0 < τ → ∃ C, 0 < C ∧
     ∀ (p : KLPar κ gmax) (σ : Fin n → Bool) (r : Fin n),
       (∀ (j : Fin n), σ j ≠ σ (j + 1)) →
         ∀ (a : Fin n → Zd d p.L),
           ∑ b, ‖∑ δ with δ r = b, KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ *
                 ∏ i ∈ Finset.univ.erase r, thetaEdge d p.L p.g (mSigma p.E) p.t (σ i) (σ (i + 1)) (a i) (δ i)‖ ≤
             C * ↑p.L ^ τ * Bparam d p.L p.g p.t 0 ^ (n - 2)
@KLindStep_nonAlt (merged, KL10a) : … ∀ (p : KLPar κ gmax) (σ : Fin n → Bool) (r : Fin n),
       σ r ≠ σ (r + 1) → (¬∀ (j : Fin n), σ j ≠ σ (j + 1)) → ∀ (a …), <same inequality>
```
- Statement: same quantifier shape as the merged `KLindStep_nonAlt` (`∀ τ > 0, ∃ C > 0, ∀ p σ r`), every alternating `σ` (both `σ_alt` and its complement), every root `r`, every `a`; the inequality is the pin's body token for token. `C` is chosen before `p`, so it depends only on `d, n, κ, gmax, τ` (DECISIONS §29); `L, g, t, E` live in `p : KLPar κ gmax`. Alternating implies `σ r ≠ σ (r+1)`, so it is exactly the pin restricted to the alternating case, as the ticket asks. For odd `n` it is vacuously true (no alternating `σ`); the endpoint `KLindStepAt_holds` covers all `n ≥ 3` (prove report (d) 3). Not a defect.
- Hypotheses: only `KLPT d κ gmax` besides the numeric ones. **PASS.**

## 4. Target 3 — `KLindStepAt_holds`, `KLindStepPin_holds`
```
KLindStepAt_holds : ∀ (d n : ℕ) [inst : NeZero n] (κ gmax : ℝ),
  3 ≤ d → 3 ≤ n → 0 < κ → 0 < gmax → KLPT d κ gmax → KLindStepAt d n κ gmax
KLindStepPin_holds : KLindStepPin
```
Ticket pin `KLindStepAt_holds : 3 ≤ d → 3 ≤ n → 0 < κ → 0 < gmax → KLPT d κ gmax → KLindStepAt d n κ gmax`: matches, binders those of `KLindStepPin`. Proof (file lines 832–850): `by_cases hσ : ∀ j, σ j ≠ σ (j + 1)`, `KLindStep_alt` / merged `KLindStep_nonAlt`, `C = C₁ + C₂`; `KLindStepPin_holds := fun d n _ κ gmax hd hn hκ hg hPT => KLindStepAt_holds …`. **PASS.**

## 5. Vacuity, hidden hypotheses, cycles
```
structure RBM.Loop.KLPar (κ gmax : ℝ) : Type
  fields: L W : ℕ, hL : 3 ≤ L, hW : 1 ≤ W, g, hg0 : 0 < g, hg1 : g ≤ gmax, E, hE : |E| ≤ 2 - κ, t, ht0 : 0 ≤ t, ht1 : t < 1
structure RBM.Loop.KLPT (d : ℕ) (κ gmax : ℝ) : Prop
  fields: decay : KLDecay d gmax, short : KLShort d κ gmax, diffOne : KLDiffOne d gmax,
          diffTwo : KLDiffTwo d gmax, zeroMode : KLZero d gmax
$ grep -n "KLPT" RBM3D/Test/Axioms.lean
79:  [`RBM.ThetaDiffOne, `RBM.ThetaDiffTwo, `RBM.PropTH, `RBM.Loop.KLPT]
```
- `KLPar` fields are the parameter domain of the pin (merged, unchanged); no estimate is hidden in a structure.
- `KLPT` is the merged, registered (borrowed) external hypothesis, the KL gate's propagator pin (DECISIONS lines 141, 148–149); the ticket names it as the only hypothesis and allows it in the instances. Limit check at the instance data is in the prove report (a) S4 (`L^d(1-t)Θ(0,0)` → 1.0000 as `1-t → 10⁻⁹`, `(1-t)·rowsum = 1`).
- No cycle: `KLindStepAt`/`KLindStepPin` are defined in this file and are used by no merged file as a hypothesis; the proof uses merged `KLIndStepA` results only. No new `open private` (grep above).

## 6. Compiled nonempty instances (file lines 857–944; compiled by the build in §0)
Data `KLinstPar : KLPar 1 1` (merged `Loop/KLTree.lean:857`): `L = 5`, `W = 2`, `g = 1/2`, `E = 0`, `t = 9/10`.
```
L870  obtain ⟨C, hC, H⟩ := KLindStep_alt 4 (by norm_num) (by norm_num) one_pos one_pos hPT 1 one_pos
L871  exact ⟨C, hC, H KLinstPar (KLsigAlt 4) 1 (by decide) ![0, 1, 2, 3]⟩
L883  … H KLinstPar (fun k => !KLsigAlt 4 k) 2 (by decide) ![![0,0,0], ![1,0,0], ![0,1,2], ![2,2,2]]⟩
L896  … KLindStep_alt 6 … ; H KLinstPar (KLsigAlt 6) 3 (by decide) ![0, 1, 2, 3, 4, 0]⟩
L922  obtain ⟨C, hC, H⟩ := KLindStepAt_holds 3 4 1 1 (by norm_num) (by norm_num) one_pos one_pos hPT 1 one_pos
L924  exact ⟨C, hC, H KLinstPar (KLsigAlt 4) 1 (by decide) ![0, 1, 2, 3],
L925    H KLinstPar (fun k => !KLsigAlt 4 k) 2 (by decide) ![0, 1, 2, 3],
L926    H KLinstPar ![true, true, true, false] 2 (by decide) ![0, 1, 2, 3]⟩
L939  refine ⟨KLindStepPin_holds 3 4 1 1 (by norm_num) (by norm_num) one_pos one_pos hPT, ?_⟩
L942  exact ⟨C, hC, H KLinstPar KLinstσ 0 (by decide) KLinsta⟩
```
- `KLindStep_alt`: `d = 3`, `n = 4` (`σ_alt`, `r = 1`; complement, `r = 2`) and `n = 6` (`r = 3`); alternation discharged by `decide`; `τ = 1`.
- `KLindStepAt_holds`: both branches of the case split, one common `C` (alternating, its complement, and non-alternating `(+,+,+,-)` with long root `2`).
- `KLindStepPin_holds`: at `(3,4,1,1)` and `(3,3,1,1)`, unfolded at `KLinstσ = (+,-,+)`, `r = 0`.
- Every deterministic hypothesis is discharged (`3 ≤ d`, `3 ≤ n`, `0 < κ`, `0 < gmax`, `KLPar` fields, `σ_r ≠ σ_{r+1}`, alternation). Only `hPT : KLPT 3 1 1` remains, which the ticket allows. Nothing degenerate: `L = 5`, `n ∈ {3,4,6}`, the index sets `Zd 3 5` and `univ.erase r` are nonempty, `0 ≤ t < 1`. Ticket requirements (`n = 4`, `KLsigAlt 4`, `r = 1`, complement at `r = 2`) met. **PASS.**

## 7. Paper deltas
Paper `(eq:ind-step-bound)` (`paper/tex/A_deterministic_estimates.tex:703–705`): `Σ_{b_1} |Σ_{b∖b_1} Σ^{(∅)} ∏_{i≥2} Θ̃_{t,a_i b_i}| ≺ B_{t,0}^{n-2}`, with `Θ̃ ∈ {Θ^{(σ,σ')}_t, tS^{(B)}Θ^{(+,-)}_t}` (`:682`), root `1` WLOG.
Lean vs paper:
1. The leaves are only `thetaEdge … (σ i) (σ (i+1))` (no `tSΘ^{(+,-)}` leaf); the root can be any `r` with `σ_r ≠ σ_{r+1}`. Inherited from the probe pin. Proposed as **T2106a**. Before this ticket `docs/paper-deltas.md` had no entry for the `Θ̃` restriction: line 459 covers only the `Theta` model, `n ≥ 4` even and `π = ∅`. → covered by the candidate.
2. `≺` is written as `∀ τ > 0, ∃ C > 0` uniform over `KLPar κ gmax` with loss `L^τ`: this is the project's standard reading. Constants are explicit (paper-deltas line 459 and D193–D196 for KL10a).
3. The `log L` pair sum is absorbed by the loss: **T2106b**. It changes no statement; the T2100 audit already judged it.
All statement differences are covered.

## 8. Observations (no RETURN)
- O1: `KLindStep_alt` holds vacuously for odd `n`. That is expected: an alternating `σ` exists only for even `n`. The instances use `n = 4, 6`.
- O2: The prove report's (a) row 2 describes `3^{n-1}` patterns. The Lean code expands only `V = ∅` a second time (the G2 terms use a crude bound on `f₁+f₀`). The report's narrative item 2 records this. It changes no statement.

## Verdict
| Target | Verdict |
|---|---|
| 1 `KLindStepAt`, `KLindStepPin` (verbatim) | PASS |
| 2 `KLindStep_alt` | PASS |
| 3 `KLindStepAt_holds`, `KLindStepPin_holds` | PASS |

**Overall: PASS.** No dispatcher sign-off needed. Paper-delta candidates T2106a (leaf-type restriction) and T2106b (proof budget, no statement change) go to the dispatcher for numbering.
