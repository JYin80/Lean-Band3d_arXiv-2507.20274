Auditor model: claude-opus-5-5

# T2360 audit, round 1 (BA-DK stage-K design, report only): PASS

Written Fri Oct  9 20:04:38 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2360-audit1`, detached at `6a3b821` (`t/T2360`).
Audited: probe `RBM3D/Probe/T2360Pins.lean`, `docs/reports/T2360-design.md`, `docs/reports/T2360-prove.md` (both reports are untracked in the main worktree).
Scratch scripts: `<scratchpad>/T2360/{ax.lean, aud/f1.py}`.

## 1. Build, axioms, forbidden tokens, diff, size limits

```
$ lake build RBM3D.Probe.T2360Pins          (audit worktree; only warnings are longLine in merged BA/KHeatDiff.lean)
Build completed successfully (3764 jobs).   EXIT 0
$ lake env lean RBM3D/Probe/T2360Pins.lean
PROBE_EXIT 0
$ grep -nwE "sorry|admit|axiom|native_decide" RBM3D/Probe/T2360Pins.lean
grep_exit 1                                   (no match)
$ lake env lean <scratch>/ax.lean             (#print axioms for all 26 declarations of the probe)
BAKBoundAt, BAKbound, precL_of_loss, bparam_comp, t0_ge, BAKbound_of_uniform, BAMLoop', BAMLoop_witness,
KernelFacts, kernelFacts_one, kernelFacts_SB, UniqS, isKLoop_unique_of_UniqS, baK_unique_of_UniqS, IndStepAbs,
KLindStepAt_iff, BAKsolve, BAKsol_isKLoopS, BAKward, BAKBoundAt_one, inst_BAKbound, Prec_of_loss, BATreeRep,
SumZeroAbs, KLsumZeroAt_iff, BATheta_swap:
  each "depends on axioms: [propext, Classical.choice, Quot.sound]"    EXIT 0
$ git diff --stat main...t/T2360
 RBM3D/Probe/T2360Pins.lean | 396 +++  1 file changed
$ git merge-base main t/T2360  -> 1fcb883 ; git diff --stat 1fcb883 main -- RBM3D/ RBM3D.lean
 only RBM3D/Graph/LW{MomExp,MomExpInf,MomentExpA,XiExp}.lean (T2359): no Loop/ or BA/ file moved, so the citations still hold
$ wc -l probe design prove
 396 RBM3D/Probe/T2360Pins.lean (<= 400)   176 docs/reports/T2360-design.md (<= 300)   294 docs/reports/T2360-prove.md (<= 300)
```

## 2. Stage-K target statement (K2) against the ticket's pin

The ticket requires the target in the shape of `STKboundgL` at the carrier `baFMz sz z`, for every flow.
Probe `:49-52`:
```
def BAKbound (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      STKboundgL (baFMz sz z) (Sizes.seqP (sz.withLam 0))
```
Merged `BA/FlowPins.lean:424-428`: `STKboundgL := ∀ τ, (∀n, 0 ≤ τ n) → (∀n, τ n < 1) → ∀ k, 1 ≤ k → PrecL sz μ (‖C.K n (τ n) p.1 p.2‖) (sz.Bctl n (τ n) ^ (k-1))`;
`Bctl = W^{-d}·Bparam d L (sz.lam n) t 0` (`Defs/Sizes.lean:214`); `Bparam = (g²+|1-t|)⁻¹((K+1)^{d-2})⁻¹ + (L^d|1-t|)⁻¹` (`Defs/Params.lean:36`) = `B_{t,0}` of `ML:Kbound` (`1_2:1054-1061`, read).
`baFM.K = BAKloop` and `baFM.S = 1` (`FlowPins.lean:479-486`). The constants come first, as in `STMainIndG` (`:565`), the law is `seqP (sz.withLam 0)` (the stated BA law, `:557`),
and `d ≥ 3` and `t ∈ [0,1)` match `ML:Kbound`. **Matches the ticket's pin.** No stronger or weaker variant is substituted: the target is the merged predicate itself.

The real-`t` and `BAReal` claim is checked by types and by compilation. `BATheta … (t : ℝ)` (`MFixedPoint.lean:515`), `IsKLoopS … (T : Set ℝ)` (`KLTree.lean:828-833`).
`BAKbound_of_uniform` (probe `:110`) compiles and uses only `BAflow_real` (`GreenSchur.lean:59`), `BAflow_lam0_window`, `t0_ge` and `bparam_comp`, with no horizon and no complex `t`.
So the K2 answer "no gap" is backed by a compiled reduction, not by prose.

Uniform form `BAKBoundAt` (probe `:38`). It uses a loss `C L^τ` that is uniform in `L ≥ 3`, `W ≥ 1`, `g ∈ (0,Λ]`, `BAReal` data and `t ∈ [0,1)`.
This is stronger than `≺`, and it is proposed as `T2360e`. It is used only as the hypothesis of the reduction, so it is not a substitute for the target.

## 3. Hidden hypotheses, vacuity, cycles

- Structures: only `KernelFacts` (`:204`, four fields `symm/real/colSum/entry`, all `Prop` facts about `S`). It is a pin and is discharged twice: `kernelFacts_one` (`S = I`) and `kernelFacts_SB` (from merged `SB_transpose`, `sum_SB_row`, `norm_SB_apply_le`). No hypothesis is hidden in a field.
- Vacuity: `BAKsol` is a `Classical.choose`, and it is `0` when no solution exists (`FlowPins.lean:281-286`, read), so `BAKbound` could hold vacuously.
  The design flags this itself (§2 (i)) and adds `BAKsolve` (probe `:281`, existence on `[0,1)` together with `(Kn2sol)`) to the closing conditions of stage K (§7.4).
  `BAKsolve`'s `n = 2` clause at `t = 0` reduces to `W^{-d} M^{(σ₁σ₂)}_{a₁a₂}`, which is the merged `BAMLoop` at `n = 2` (consistent, and it agrees with F1's "no difference at `n = 2`").
- Cycles: the probe imports only merged modules (`Loop.KLFinal`, `Loop.KLWard`, `BA.GreenSchur`, `BA.Prop6Path`, `BA.KKernel`). The unproved stage-K content enters only as the explicit hypothesis `U` of `BAKbound_of_uniform` / `inst_BAKbound`.

## 4. Compiled nonempty instance

`inst_BAKbound` (probe `:343-347`) applies `BAKbound_of_uniform` at:
- `d = 3`, `sz0`, `zSeq`;
- `κ = 1/2`, `ε = 1/10`, `𝔡 = 1/10`, `𝔠 = 1/6`.

Every deterministic hypothesis is discharged: `3 ≤ d` by `le_rfl`, the positivity side conditions by `norm_num`, and `BAFlow` by the merged `flow_sz0`. Only `U`, the stage-K rows K00-K12, stays as a hypothesis, which §4 step 2 allows.
The data are nondegenerate: `n = 0` of `sz0` gives `L = 4`, `W = 32`, `g = 1/64`.

Other declarations:
- `BAKBoundAt_one` is unconditional, so it is its own instance.
- `BAMLoop_witness` is a concrete `Z_3` evaluation (14 against 15).
- The `Iff.rfl` re-derivations `KLindStepAt_iff` and `KLsumZeroAt_iff`, and the band and BA consumers `isKLoop_unique_of_UniqS` and `baK_unique_of_UniqS`, all compile.

## 5. Finding F1, independently checked

The paper's `(eq:KMloop)` (`1_2:1003`) is `tr ∏ M(σ_i)E_{a_i}`. Expanding the trace gives `∏ M(σ_i)_{a_{i-1}a_i}`, which is the primed form.
The merged `BAMLoop` (`FlowPins.lean:274-276`, read) zips `σ` with `a.zip (a.rotate 1)`, that is `M(σ_i)_{a_i a_{i+1}}`.
The merged cut `cutGlueL` (`TreeRep.lean:75-78`) gives the inserted label `b` the charge `σ_k` of the edge ending at it, which is the paper's convention and agrees with `A:571`.
Auditor's own check (`python3 -I <scratch>/aud/f1.py`; `W = 1`, `q = 4`, random symmetric `M(+)`, `M(-) = conj M(+)`, `σ = (+,+,-)`, `a = (0,1,3)`):
```
|tr - BAMLoop'| = 0.0  |tr - BAMLoop| = 0.112602  |tr| = 0.087868
```
**F1 is confirmed:** the merged `BAMLoop` is not `(eq:KMloop)` for `n ≥ 3` with mixed charges. The design's response is in scope for a design ticket:
- it reports the gap rather than pinning around it (ticket K2);
- it proposes repair row K00 and the paper-delta candidate `T2360a`;
- it puts the repair mode to the supervisor and dispatcher (§7.1).

Consequence for the audit: `U` in `inst_BAKbound` is stated on the merged `BAMLoop`, and the design says this explicitly (§4 "Instance"). This does not invalidate the reduction, which is independent of the initial data.

## 6. K1-K6 coverage (evidence spot-checked)

```
$ wc -l <19 band KL files> | tail -1      ->  16777 total      (design §1: 16777)
$ cat <19 files> | grep -c kProd           ->  kProd: 0         (design: 0)
$ grep -n sbKernel <19 files>              ->  KLWard.lean:998 only (design: once, :998)
$ grep -noE "SB_…|sum_SB_row|norm_SB_apply_le|sbKernel…" KLUnique/Unique/KLWard | uniq -c
  KLUnique: norm_SB_apply_le 4, SB_apply_add_right 2, SB_transpose 3
  KLWard:   norm_SB_apply_le 3, SB_apply 1, SB_row 1, SB_transpose 2, sbKernel_eq_ofReal 1, sum_SB_row 1
  Unique:   norm_SB_apply_le 2, SB_row 1
```
These match the design's statement of which facts of `S` the (g) files use: symmetry, column sums, reality, the entry bound, and for `KLUnique` translation invariance.
- **K1:** table of 19 files with classes R/G/T/X (design §1). Band consumers of the (g) files are named, with the re-derivation for each; three of them are compiled (`isKLoop_unique_of_UniqS`, `KLindStepAt_iff`, `KLsumZeroAt_iff`).
- **K2:** see §2 above.
- **K3:** each paper status was checked against the TeX:
  - `A:592` "Lemma 4.16 of [RBSO1D]", stated for `n ≥ 4`: gap;
  - `A:654` one-sentence pure-loop argument: complete;
  - `A:728-734` cited to `[YY_25]`/`[RBSO1D]`: gap;
  - `1_2:1043-1046` `lem_WI_K` cited: gap, class (g).
  `SumZeroAbs` matches `(eq:Sigma-empty-sum-zero)` (slice `δ 0 = x`, `O(1-t)` and `O(g²+1-t)`). `BAKward` matches `(WI_calK)` with the shape of the band `KLK_ward` (`KLWard.lean:1123`).
- **K4:** 26 compiled declarations, row table (16 rows, 12.7k central [9.2k .. 20.3k]), exponent table, compiled instance.
- **K5:** flag raised (16 > 12), with reasons file by file (design §5).
- **K6:** row count 16, flag 24.

## 7. Paper-delta coverage

Each Lean/paper difference in the probe has a candidate:
- `BAMLoop` against `(eq:KMloop)`: `T2360a`;
- the `(f-internal2)` chord at `S = I` and the `M`-edge region rule: `T2360b`;
- `Θ^{(σ₁σ₂)} = Θ^{(σ₂σ₁)}`: `T2360c`;
- `BATreeRep` at `n ≥ 3` against the paper's `n ≥ 4`: `T2360d`;
- `BAKBoundAt` loss stronger than `≺`: `T2360e`.

`BAKbound` itself uses `B` at `sz.lam n` rather than `g₀`. This is the convention of the merged `STKboundgL`, not a new difference, and the design handles it in K2 through `bparam_comp`.
`grep -c T2360 docs/paper-deltas.md` gives 0, as expected: the dispatcher assigns the numbers.

## 8. Observations (no statement, instance, build, axiom or delta impact)

- O1. Both reports are in the main worktree, so `git diff --stat main...t/T2360` lists only the probe. The ticket's acceptance line says "the probe and the report"; the project's convention (CLAUDE.md §2; T2348/T2356) keeps reports in the main worktree. The report-only merge (CONTROL H149) brings them in.
- O2. Row K02's "generic Ward over `KernelFacts`" has no pinned generic statement in the probe; only the BA endpoint `BAKward` and `KernelFacts` are pinned. That is enough for the design, and the generic statement is a K02 ticket item.
- O3. The decisions in design §7 (F1 repair mode, route G in place, the TEAM §3 status of K05/K08, the closing conditions) are inputs to the stage-K opening REQ, which the ticket already routes through the dispatcher to the supervisor. They do not block this report-only merge.

## Verdict

**T2360: PASS.**
- The target `BAKbound` matches the ticket's pin (the merged `STKboundgL` at `baFMz`).
- The reduction and its nondegenerate `d = 3` instance compile.
- Only the three standard axioms appear, and there are no forbidden tokens.
- The diff contains only the probe, and both size limits are met.
- K1-K6 are answered with file:line evidence.
- F1 is real and is reported, not pinned around.
