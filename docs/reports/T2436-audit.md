Auditor model: claude-opus-5-5

# T2436 audit (round 1): BA-TL TL1b, `BATwistAvgProd` from `BATwistAvgRec`

Started Mon Oct 12 03:31:02 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2436-audit1`, detached at `t/T2436` = `9341551`; `main` = `8a05c54`.

## 1. Diff and declarations
```
$ git log --oneline main..t/T2436
9341551 T2436: TwistAvgB: instances of baTwistAvgProd_holds and of the conclusion, helper privacy
36909dd T2436: TwistAvgB: S1, Bctl ceiling and absorption, Markov and union per size, baTwistAvgProd_of_rec, baTwistAvgProd_holds
$ git diff --name-status main...HEAD
A	RBM3D/BA/TwistAvgB.lean
$ grep -nE "^(theorem|lemma|def|abbrev|instance)" RBM3D/BA/TwistAvgB.lean
444:theorem baTwistAvgProd_of_rec : T2427_TL1b := by
451:theorem baTwistAvgProd_holds (d : ℕ) : BATwistAvgProd d :=
```
All other declarations are `private theorem TwistAvgB_*` (lines 53, 126, 185, 235, 240, 251, 273, 289, 313, 330, 338, 387). Only sole writable file touched; `RBM3D.lean` not in the diff (the hub adds the import at merge). No frozen signature, pin or `Test/Axioms.lean` touched (registry: none, as the ticket says).

## 2. Statement (targets 1, 2) against the pin
The targets are stated *as* the pinned Props, so the statement check is definitional. The pins (on `main`, unchanged by the diff):
```
RBM3D/BA/TwistAvgA2.lean:1219  def T2427_TL1b : Prop := ∀ d, BATwistAvgRec d → BATwistAvgProd d
RBM3D/BA/TwistPins.lean:154    def BATwistAvgProd (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0)
      LWAvgLawgL (baFMz sz z) μ t → STLmaxgL (baFMz sz z) μ t → BATwistAvgLaw (baFMz sz z) μ t
```
Script check of the acceptance terms and of the pinned unfolding (auditor's scratch file, compiled in the audit worktree):
```
$ cat ax.lean
import RBM3D.BA.TwistAvgB
open RBM.BA
example : T2427_TL1b := baTwistAvgProd_of_rec
example : ∀ d, BATwistAvgProd d := baTwistAvgProd_holds
example : T2427_TL1b ↔ ∀ d, BATwistAvgRec d → BATwistAvgProd d := Iff.rfl
#print axioms RBM.BA.baTwistAvgProd_of_rec
#print axioms RBM.BA.baTwistAvgProd_holds
$ lake env lean ax.lean; echo "exit $?"
'RBM.BA.baTwistAvgProd_of_rec' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baTwistAvgProd_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```
Target 1 has exactly the type `T2427_TL1b`; target 2 has exactly `(d : ℕ) → BATwistAvgProd d`. No extra hypothesis, no weakening, quantifier order is the pin's (`K` of `BATwistAvgRec` before `𝔠, sz, z`; `ε'` chosen inside `BATwistAvgRecAt` after `𝔠`, which is allowed by the pin's quantifier order). The conclusion `BATwistAvgLaw` is `PrecL` over all ordered pairs `Zd × Zd` with bound `Bctl n (τ n)`, per `τ`, as the ticket specifies ("No net", T2413 §5).

Proof route against the ticket's plan (read at `TwistAvgB.lean:387-441`): `p = ⌈(D+4)/τ⌉₊`, `D' = 2p+2` (`hrec p hp1 ε' (2*p+2)`), `ε' = d·min(c, τ/2)` with `c = min(2𝔡𝔠, ε)/2`, eventual absorption (`TwistAvgB_absorb`), floor `N⁻¹ ≤ Bctl` (`cont_inv_size_le_Bctl`, merged), S1 at the maximizer (`TwistAvgB_Xmax_le`), Markov with integrability from `twAvgReg_holds`, union over pairs with `card ≤ N²` (`TwistAvgB_step`, `TwistAvgB_card_le`). Matches the ticket's target 1 plan; target 2 is `baTwistAvgProd_of_rec d (baTwistAvgRec_holds d)` as pinned.

## 3. Hidden hypotheses, vacuity, cycles
- No new structure, no new `def`; the only premises are the pin's. `BAFlow`, `LWAvgLawgL`, `STLmaxgL` are merged definitions used unchanged.
- No `STLKgL`/`BAGbEXP*` premise: the only occurrence is a docstring.
```
$ grep -n "STLKgL\|BAGbEXP" RBM3D/BA/TwistAvgB.lean | cut -c1-80
386:No net, no `STLKgL`/`BAGbEXP*`: the premises are those of `BATwistAvgRecAt`, in
```
- Dependencies are merged results on `main`: `baTwistAvgRec_holds` (`BA/TwistAvgA2.lean:1040`), `twAvgReg_holds` (`BA/TwistAvgA.lean:613`), both imported by `RBM3D.lean:476-477`; last main commit touching `TwistAvgA2.lean`: `3e4b094`. The new file imports only `RBM3D.BA.TwistAvgA2` (line 6) and nothing imports it: no cycle.
- External hypotheses `LWAvgLawgL`, `STLmaxgL` are other gates' pins (ticket target 3 keeps them as hypotheses). Limit check: the report's (a) gives concrete `Bctl_n` (`6.2e-5, 1.9e-9, 4.3e-12, 5.7e-14`, `n = 0..3`) and `1/N_n` along `sz0`, `t = 1/2`, showing `Bctl ≥ N⁻¹` (the ≺-floor) and `Bctl → 0`; no contradiction between the two pins at `k = 1` (`STLmaxgL` bound `Bctl^0 = 1`).

## 4. Compiled nonempty instance (target 3)
`TwistAvgB.lean:468-472` (target 2 at the datum) and `:474-480` (target 1's core at the datum):
```
example (hA : LWAvgLawgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hM : STLmaxgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) :
    BATwistAvgLaw (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) :=
  baTwistAvgProd_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) hA hM
```
Data: `d = 3`, `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`; `N = 2097152` at `n = 0`), `zSeq`, `flow_sz0 : BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq` (merged, `BA/FlowPins.lean`), `t ≡ 1/2` with `0 ≤ t` by `norm_num` and `t ≤ T₀` by merged `half_lt_t0`. Every deterministic hypothesis (`3 ≤ d`, positivity of `κ, ε, 𝔡`, `BAFlow`, the two time bounds) is discharged; only `hA`, `hM` (other gates' pins) remain, as the ticket allows. Nondegenerate: `L ≥ 4`, `W ≥ 32`, `t = 1/2 ∈ (0, T₀)`. In addition `:483-498` derives from the conclusion at `(τ, D) = (1/2, 1)` that eventually some `ω` satisfies the bound for all `(4(n+1))^6` pairs (probability measure, bad set `≤ N⁻¹ < 1`), so the conclusion is not vacuous. The whole file compiles (section 5).
The two acceptance `example`s are at `:464-465` and were re-compiled independently (section 2).

## 5. Build, axioms, hygiene, check file
```
$ lake build RBM3D.BA.TwistAvgB 2>&1 > build.log; grep -c "^error" build.log; grep "TwistAvgB" build.log | grep -E "error|warning" | head; tail -1 build.log
0
Build completed successfully (4008 jobs).
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom" RBM3D/BA/TwistAvgB.lean | wc -l
       0
$ lake env lean /Users/junyin/Lean_proof/RBM3D/docs/tickets/checks/T2436-check.lean >/dev/null 2>&1; echo "check exit $?"
check exit 0
$ wc -l RBM3D/BA/TwistAvgB.lean
     504 RBM3D/BA/TwistAvgB.lean
```
Axioms (section 2): the standard three for both public theorems. 504 lines against the stop line 1,500. Full `lake build` is the hub's at merge.

## 6. Paper deltas
`grep -n "BATwistAvgLaw\|TL1\b\|T2427a\|T2413" docs/paper-deltas.md` returns nothing; the Lean/paper differences of this ticket are proposed in the prove report (d):
- **T2436a** (T.7 Step 5, `T2398-TL-proofs.md:89-90`): S1 via `B ≥ N⁻¹` and `D' = 2p+2`; constant `C' = (4p+2)K+2`; no additive `2N^{-D/2}`; `ε'` depends on `𝔠` (`d·min(c, τ/2)`) rather than "`ε < 𝔡/2`".
- **T2436b** (Step 6, `:92`): per `τ`, per ordered pair, level `N^τ B` with probability `N^{-D}` (the `≺` of `PrecL`) instead of `W^{2ε}W^{-d}B` with `W^{-D}`; no union over the two signs and no `N^{-C}`-net in `u` (the uniform-in-`u` lift is the consumer's, T2413 §5).
These cover every difference between the Lean statements and T.7 Steps 5-6 I found; the statement-level ones (per `τ`, one charge, no net) are inherited from the pin `BATwistAvgLaw` and are restated in T2436b.

## 7. Observations (no verdict effect)
- O1. The (a) exponent table (rows 2-4, 7, and the `n*` observation) describes a route not used by the Lean proof (`c₀ = (𝔡⁻²+1)⁻¹`, `ε' = min(𝔡, dε/2, dτ/2)`, square-root `C'`); this is recorded in (a′) items 1-3, and the built constants are stated in (b). No statement effect.
- O2. The file sets `linter.flexible false`, `linter.unusedVariables false` and similar options; compiles without errors; no effect.

## Verdicts
| Target | Verdict |
|---|---|
| 1 `baTwistAvgProd_of_rec : T2427_TL1b` | **PASS** |
| 2 `baTwistAvgProd_holds (d) : BATwistAvgProd d` | **PASS** |
| 3 instance at `sz0`, `zSeq`, `flow_sz0`, `t ≡ 1/2` | **PASS** |
| 4 registry: none (no change to `Test/Axioms.lean`) | **PASS** |

Overall: **PASS**. No dispatcher sign-off needed.
