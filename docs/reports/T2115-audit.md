Auditor model: claude-opus-5-5
# T2115 audit (round 1) — Sun Oct  4 07:01:49 UTC 2026 (`date -u`)
Branch `t/T2115` at `177e4e3`, audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2115-audit1` (detached). Merge base `778bdf7`; main has 5 later commits, none touching `RBM3D/Loop/`.

## 1. Statement: pins against the check file (script diff)
```
$ awk '/^\/-- \*\*`\(eq:bcal_k\)`/{f=1} f{print} /KLKpiBoundAt d n κ gmax$/ && f{exit}' <file> > pin_*.txt   # check file vs KLInduct.lean
      29 pin_check.txt
      29 pin_file.txt
$ diff pin_check.txt pin_file.txt && echo PIN-IDENTICAL
PIN-IDENTICAL
```
That covers the four pinned `def`s `KLBoundAt`, `KLboundPin`, `KLKpiBoundAt`, `KLKpiBoundPin` (docstrings included). Endpoint statements (from the file):
```
L1150 theorem KLKpiBoundPin_holds : KLKpiBoundPin
L1190 theorem KLboundPin_holds : KLboundPin
L987  theorem KLKpi_step (d n) [NeZero n] (κ gmax) (hd : 3 ≤ d) (hn : 3 ≤ n) (hκ : 0 < κ) (hg : 0 < gmax) (hPT : KLPT d κ gmax)
        (hout : ∀ (n'' : ℕ) [NeZero n''], 3 ≤ n'' → n'' < n → KLKpiBoundAt d n'' κ gmax) : KLKpiBoundAt d n κ gmax
L609  theorem KLKpi_cut ... (hL : 3 ≤ L) (hn : 3 ≤ n) (hm : ∀ s s', ‖(t:ℂ) * (m s * m s')‖ < 1) (hF₀ : F₀ ∈ TSP n)
        (hπ : KLFlong F₀ σ = π) (hJπ : J ∈ π) (hinner : ∀ e ∈ π, KLArcLe e J → e = J) (a) :
        KLKpi d L g m t σ a π = ∑ u, ∑ w, t * (∑ δ ∈ univ.filter (δ (Fin.last _) = u), KLSigmaPi … (sigmaIn σ J) ∅ δ *
          ∏ i ∈ univ.erase (Fin.last (KLwIn J)), thetaEdge … (aIn J a i) (δ i)) * SB d L g u w * KLKpi … (sigmaOut σ J) (aOut J a w) ((π.erase J).image (KLshiftOut J))
L226/236/267 KLBoundAt_one (hκ) / KLBoundAt_two (hκ) (hPT : KLPT d κ gmax) / KLBoundAt_three (hκ) (hPT : KLPT (k+2) κ gmax)
```
Inner summand of `KLKpi_cut` vs the merged `KLindStepAt` (`KLIndStepB.lean:55-62`):
```
∑ b, ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d p.L => δ r = b),
    KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ * ∏ i ∈ Finset.univ.erase r, thetaEdge … (σ i) (σ (i + 1)) (a i) (δ i)‖
```
Same summand at `n := KLwIn J + 1`, `r := Fin.last`, `σ := sigmaIn σ J`, `a := KLInduct_aIn J a`: target 3 as specified (T2106a answered: `KLindStepAt` as merged suffices; no `tSΘ` leaf). The factor is exactly `t`, not the ticket's "modulus 1, `∏ m`" (T2115b).
- Quantifier order (`∀ τ, ∃ C, ∀ p σ π a`), loss `L^τ`, `B_{t,0}^{n-1}`, `((W^d)⁻¹ B)^{n-1}`, ranges `n ≥ 3` / `n ≥ 1`, `3 ≤ d`: fixed by the verbatim pins.
- `KLboundPin_holds` covers every `n ≥ 1` (`n = 1,2,3` from target 1, `n ≥ 4` from `KLInduct_BoundAt_of_Kpi`); `KLKpiBoundPin_holds` covers every `n ≥ 3` by `Nat.strong_induction_on` over `KLKpi_step` (L1138-1146). Both are the general pins, not special cases.

## 2. Hidden hypotheses, vacuity, cycles
- Hypotheses of the endpoints: `3 ≤ d`, `3 ≤ n`/`1 ≤ n`, `0 < κ`, `0 < gmax`, `KLPT d κ gmax`. `KLPar` (`KLTree.lean:250`) fields are the parameter domain `3 ≤ L, 1 ≤ W, 0 < g ≤ gmax, |E| ≤ 2-κ, 0 ≤ t < 1`, inhabited by `KLinstPar` (`KLTree.lean:857`). `KLPT` (`KLTree.lean:321`) bundles `KLDecay, KLShort, KLDiffOne, KLDiffTwo, KLZero` and is in `borrowedProps` (`Test/Axioms.lean:79`), as the ticket requires. Limit check of `KLPT`: prove report (a)(ii), `pre2.py` lines (`L^d(1-t)Θ(0,0) → 1`, row sums `= 1`, bounds stable as `1-t → 0`).
- No new `Prop`: the only `def`s are the four pins and the instance data (`KLInduct_aIn/aOut/instσ/insta/instJ`). Dependencies are merged (`KLindStepPin_holds`, `KLsum_cut`, `KLtreeValW_cut`, `KLK_eq_sum_Kpi`, `KLmolecule_holds`, private `KLSumZeroWard` lemmas via `open private`). No cycle: `KLKpi_step` takes `P(n'')` for `n'' < n` only, discharged by the strong induction.
- Registry pre-check (audit worktree; cache from main, the hub's full build is authoritative):
```
$ printf "import RBM3D\nimport RBM3D.Loop.KLInduct\n#assert_rbm_axioms\n" | lake env lean --stdin | grep -E "error|axiom audit|KLPT|premises found|KLoopBound"
axiom audit: 3636 theorems, 1284 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.Loop.KLPT: 15 [no certificate]
  RBM.Loop.KLoopBound: 0 [no certificate]
premises found by scanning: 81 (borrowed 2, owed 63, structural 16).
exit=0
```

## 3. Compiled nonempty instances (in `KLInduct.lean` §8, compiled by the module build below)
Data: `KLinstPar` = (`L = 5, W = 2, g = 1/2, E = 0, t = 9/10, κ = gmax = 1`), `d = 3`, `σ = (+,+,-,-)`, labels `![![0,0,0],![1,0,0],![0,1,2],![2,2,2]]`, `τ = 1`. Only `hPT : KLPT 3 1 1` is left as a hypothesis (another gate's borrowed pin, allowed).
| endpoint | example (lines) | data | degenerate? |
|---|---|---|---|
| `KLKpiBoundPin_holds` | 1219-1233 | `n = 4`, `π ∈ {∅, {(0,2)}, {(1,3)}}` | no |
| `KLboundPin_holds` | 1238-1267 | `n = 4, 3, 2, 1` | no |
| `KLBoundAt_one/two/three` | 1271-1291 | `n = 1, 2, 3`, distinct labels | no |
| `KLKpi_step` | 1300-1317 | `n = 4`, `hout` discharged by `KLInduct_KpiBoundAt_holds 3 3` | no |
| `KLInduct_Kpi_empty_bound` | 1320-1335 | `n = 4, 5` | no |
| `KLKpi_cut` | 1340-1361 | `n = 4`, `J = F₀ = π = {(0,2)}`; `hm`, `hF₀`, `hπ`, `hJπ`, `hinner` discharged (`norm_mul_mSigma_lt_one`, `TSP_four`, `decide`); no hypothesis left | no |
| `KLedge_sup`, `KLedge_l1`, `KLstar_le`, `KLone_le_rpow`, `KLTheta_eq_zero` | 1365-1393 | concrete | no |
These are the instances the ticket asks for (`KLKpiBoundAt`, `KLBoundAt` at `n = 4` from the two `_holds`, `KLBoundAt_three` at the same data).

## 4. Build, axioms, hygiene, diff
```
$ lake build RBM3D.Loop.KLInduct
Build completed successfully (3257 jobs).
$ lake env lean ax.lean     # #print axioms
'RBM.Loop.KLKpiBoundPin_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLboundPin_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLKpi_cut' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLKpi_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLInduct_KpiBoundAt_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLInduct_BoundAt_of_Kpi' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLInduct_Kpi_empty_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLBoundAt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLBoundAt_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLBoundAt_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLedge_sup' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLedge_l1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLstar_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLone_le_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLTheta_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ grep -nE "sorry|admit|native_decide|^\s*axiom|maxHeartbeats" RBM3D/Loop/KLInduct.lean; echo grep_exit=$?
grep_exit=1
$ git diff --stat main...HEAD
 RBM3D/Loop/KLInduct.lean | 1397 ++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1397 insertions(+)
$ name clash of the 24 public names vs `git grep` on current main (RBM3D/): total clashes in main: 0
```
Only the sole writable file `RBM3D/Loop/KLInduct.lean` is touched (`Test/Axioms.lean` untouched; no line needed). No frozen signature or merged file changed. Imports: `Batteries.Tactic.OpenPrivate`, `RBM3D.Loop.KLIndStepB`, `RBM3D.Loop.KLCut` (not `RBM3D`).

## 5. Paper deltas
| difference | coverage |
|---|---|
| induction over polygon vertices / innermost long edge, for the standard `K^{(π)}` only, vs the paper's induction over molecules for `K̃^{(π)}` (`A:678-680, 791-805`) | candidate T2115a |
| cut prefactor `t` (ticket text) | candidate T2115b (ticket, not paper) |
| `KLedge_sup`, `KLBoundAt_two/three` take `KLPT` instead of the probe's `KLDecay`/`KLShort` | candidate T2115c; makes the existing entry at `paper-deltas.md:711` ("`KLBoundAt_three` uses `KLDecay` and `KLShort`") out of date — the dispatcher should update it with T2115c |
| loss `L^τ` uniform in `g, E, t, σ, a` (stronger than `≺`) | existing entry, `paper-deltas.md:723` |
| `KLindStepAt` leaves/root (T2106a) | existing D214 (`paper-deltas.md:867-869`), answered by T2115a |
Every Lean/paper statement difference is covered.

## Observations (no verdict effect)
- Prove report (b) quotes 3511 theorems for the registry run; the audit run shows 3636 because the copied build cache is from the newer main. Both runs exit 0 with no error.
- `KLoopBound` (`KBound.lean:74`) is implied by `KLboundPin` for `K := KLK … E`, as report item 9 says (same `∀ τ ∃ C` form, uniform in `t, σ, a`). No bridge theorem is written; as the ticket asks, the report states the implication. KL14 decides.

## Verdicts
- Target 1 (`n ≤ 3` port; merged twins `KLIndStepA_Bparam_nonneg/_le_zero` reused): **PASS**.
- Target 2 (pins verbatim): **PASS**.
- Target 3 (`KLKpi_cut`, `KLKpi_step`; T2106a answered): **PASS**.
- Target 4 (`KLKpiBoundPin_holds`, `KLboundPin_holds`, conditional only on `KLPT`): **PASS**.
**Overall: PASS.** No dispatcher sign-off is needed (the update to the `paper-deltas.md:711` text is ordinary delta numbering under T2115c).
