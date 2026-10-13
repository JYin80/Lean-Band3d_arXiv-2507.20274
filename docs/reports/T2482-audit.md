Auditor model: claude-opus-5-5
# T2482 (U U5b-1: `BA/Step5IIIEdet`, targets 1-5, 8 (a)) audit round 1 — Tue Oct 13 03:47:22 UTC 2026
Inputs: ticket `docs/tickets/T2482.md`; `T2482-prove.md` (a), (a″), (b)-(d); `T2482-1a-audit.md` §6 (split confirmed: only U5b-1 here);
branch `t/T2482` e1cfd825 (base a2f86197). Worktree: detached `/Users/junyin/Lean_proof/RBM3D-wt/T2482-audit1` (cache `cp -c`).
Scratch: `<scratchpad>/T2482/aud1/` (`aud.lean`, `pre.lean`, outputs). I edited no source file.

## 1. Diff, build, axioms, hygiene
```
$ git diff --stat main...t/T2482
 RBM3D/BA/Step5IIIEdet.lean | 1493 ++++++++++++
 RBM3D/Probe/T2482Pins.lean |  395 ++++          (1a probe; sole writable for 1a only, never merged)
$ lake build RBM3D.BA.Step5IIIEdet; echo exit $?
✔ [3850/3850] Built RBM3D.BA.Step5IIIEdet (13s)
Build completed successfully (3850 jobs).
exit 0
$ grep -c "Step5IIIEdet.lean" build.out          # warning/error lines of the new file
0
$ grep -nE "sorry|admit|native_decide|^\s*axiom" RBM3D/BA/Step5IIIEdet.lean; echo rc=$?
rc=1
$ grep -nE "^(theorem|lemma|def|abbrev|noncomputable def) " Step5IIIEdet.lean | grep -vE " (baStep5IIIE_|BAStep5IIIE|Step5IIIEdet_)"; echo rc=$?
rc=1                                               # every public name is pinned or carries the stem (rule (E)); 12 private
$ git grep -l Step5IIIEdet -- RBM3D RBM3D.lean | grep -v "BA/Step5IIIEdet.lean\|Probe/"; echo rc=$?
rc=1                                               # no importer; no import of the probe
$ lake env lean aud.lean   (10 "#print axioms", see §2)
baStep5IIIE_trace_mul_le / _trace_mul3_le / _trace_prod_le / _loop_hs / _loop_hs_list / _loop_glue / _lk / _wG,
Step5IIIEdet_scalar_sz0_one / _scalar_sz0_800: each "depends on axioms: [propext, Classical.choice, Quot.sound]"   (10 of 10)
```
Imports: `Chain/Step2Gen`, `BA/Step2BA`, `Loop/GLoopFlow`, `Induction/Step5Pins`, `Path/LemDecCalE`, `Path/LemDecCalEwG`,
`Graph/BAAuxGraph2` (all merged; the last one accepted at the 1a-audit, O2). `open private` (L43): two lattice lemmas of
`Path/LemDecCalE` (`zdistInf_sub_comm`, `zdistInf_tri_real`); no merged file is edited, no `private` deleted.

## 2. Statements against the pins (compiled; my file `aud.lean`)
`aud.lean` = the check's imports + `import RBM3D.BA.Step5IIIEdet`, the check's pins (`T2482-check.lean:110-227`, verbatim),
the list/glue texts fixed at the 1a-audit (`git show 0ac2aab8:RBM3D/Probe/T2482Pins.lean`, lines 113-130, verbatim), then:
```
example : T2482_TraceMulLe := fun ι _ _ A B => baStep5IIIE_trace_mul_le A B
example : T2482_TraceMul3Le := fun ι _ _ A B C => baStep5IIIE_trace_mul3_le A B C
example : T2482_TraceProdLe := fun ι _ _ l hl => baStep5IIIE_trace_prod_le l hl
example : ∀ d, T2482_LoopHS d := fun d sz lam0 E n u H hH k σ a hk => baStep5IIIE_loop_hs d sz lam0 E n u H hH k σ a hk
example : ∀ d, T2482_LoopHSList d := fun d sz lam0 E n u H hH k σ a hk => baStep5IIIE_loop_hs_list d sz lam0 E n u H hH k σ a hk
example : ∀ d, T2482_LoopGlue d := fun d sz lam0 E n u H hH σ a p => baStep5IIIE_loop_glue d sz lam0 E n u H hH σ a p
example : @T2482_BAScalar = @BAStep5IIIEScalar := rfl
example : @T2482_BAMatrix = @BAStep5IIIEMatrix := rfl
example : ∀ d, T2482_EdetLk d := fun d hd sz lam0 E n u D Λ K₀ J θ Cd H hθ hCd hs hm => baStep5IIIE_lk d hd sz lam0 E n u D Λ K₀ J θ Cd H hθ hCd hs hm
example : ∀ d, T2482_EdetWG d := fun d hd sz lam0 E n u D Λ K₀ J θ Cd H hθ hCd hs hm => baStep5IIIE_wG d hd sz lam0 E n u D Λ K₀ J θ Cd H hθ hCd hs hm
example : ∀ d : ℕ, T2482_EdetLk d → T2482_EdetWG d → T2482_EdetDif d → T2482_BAEdet d := ...   -- U5b-2 can assemble from these
$ lake env lean aud.lean; echo exit $?
exit 0          (output: only unused-variable linter warnings on my own binders `ι`, `d`; no error)
```
So every U5b-1 target has exactly its pinned type, with the bundle definitionally equal (`rfl`) to the check's texts.
Read against the paper (`3_5:2315-2333`) and the ticket:
- **Hypotheses.** `lk`/`wG`: `3 ≤ d`, `0 < θ`, `0 < Cd`, scalar bundle (`0 ≤ u < 1`, `0 < lam`, `lam² ≤ 1-u` = paper's
  `1-t ≥ λ²`, `1 ≤ lam²W^d`, `1 ≤ Λ, K₀`, `log W ≥ 4`, floor `(L^dW^{6d})² ≤ W^D`, `1 ≤ J ≤ W^{1/2}`), matrix bundle
  (i)-(vi). No `|E| < 2`, no entry bound of `G`, no `M = mI`, no `SB d` (greps §4). Conclusion: all `σ`, `a`, uniform in `u`.
- **Losses.** `≺` is the explicit `lossE2wG d L W Λ K₀`; RHS factors `(1-u)⁻¹(W^d|1-u|)⁻¹J²` (lk) and
  `(1-u)⁻¹(1(r ≤ 2ℓ*) + (W^d|1-u|)^{-1/2}J^{3/2})` (wG) match `res_deccalE_lk`, `res_deccalE_wG` except the cut `2ℓ*` (T2459b).
- **Target 2** (HS, list, glue) only needs `H.IsHermitian`, any `k ≥ 2`, any `lam0 E`; the `k ≥ 2` restriction is necessary
  (k = 1 false, `√8` ratio, 1a numerics).
- Not a special case: the targets are the general deterministic statements of the pins; `dif`, `S_θ`, `BAStep5IIIEdet`
  (targets 6-7, 8 (b)) are U5b-2 by the confirmed split and are not claimed here.

## 3. Hidden hypotheses, vacuity, cycles, instances
- The bundle is two `Prop` definitions with visible conjuncts (no structure fields). The external hypothesis is the matrix
  part (U5c's good event; ticket answer (4), audit O2); its limit check is the `u = 0`, `G = M`, Neumann-tail argument with
  `n → ∞` exponent comparison of prove report (a) l. 59 (accepted at the 1a-audit, O3). Unread conjuncts: (ii), (v) k=4,6,
  (vi) (for U5b-2), `0 < lam`, `J ≤ W^{1/2}` (prove (b) hypothesis table; harmless, but see §5).
- No cycle: the file imports only merged modules; nothing of T2481/U5c-U5e or the probe.
- Instances in the file (L1385-1493, compiled by the build in §1):
  - target 1 at three concrete non-commuting `2×2` complex matrices (`trace_mul_le`, `_mul3_le`, `_prod_le`, length 3);
  - target 3 scalar part proved at `sz0`, `u = 1/2`, `D = 40`, `Λ = K₀ = J = 1`: `n = 1` (`L = 8`, `W = 1024`) and
    `n = 800` (`L = 3204`, `W ≈ 1.06e16`, `6ℓ* ≤ L/2`: every window nonempty), theorems `Step5IIIEdet_scalar_sz0_one/_800`;
  - target 2 at `H = 0` (k = 3, 6) and at `seqHflowBA` (Hermitian discharged by `BAAuxGraph2_seqHflowBA_herm`); list (k=3)
    and glue forms at `H = 0`, carrier `baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)`;
  - targets 4, 5 at `n = 800` (and `lk` at `n = 1`), scalar part discharged by the witnesses, `θ = 1/10`, `Cd = 1` discharged by
    `norm_num`; the matrix part a hypothesis, as the ticket's target 8 and answer (4) allow.
  No `N = 0`, empty index, collapsed window (the `n = 800` instance fixes the 1a's F1), or `False` premise.

## 4. Greps (new file)
```
$ grep -nE 'BAK_le_small|BAMB_upper_small|BAGbEXP|Mbound_AO|W\^\(-eps|BAm_im_lower_window' RBM3D/BA/Step5IIIEdet.lean; echo rc=$?
rc=1
$ grep -nE 'STGridRepNgL|withLam|\|E\||norm_mE|mSigma|SB d|E2Hyp|gexRHS|STGMMg|≤ A \*' RBM3D/BA/Step5IIIEdet.lean; echo rc=$?
rc=1
$ grep -nE "lam0 ≤|lam0 n ≤|gK" RBM3D/BA/Step5IIIEdet.lean; echo rc=$?          # UBA-C1 crossing
rc=1
```

## 5. Whole-library axiom audit (the merge build) — the defect
The ticket's acceptance criterion says `import RBM3D` + `#assert_rbm_axioms` passes with `Test/Axioms.lean` unchanged, and
"Registry: none". In the audit worktree, after `lake build RBM3D` (exit 0, 4330 jobs):
```
$ printf 'import RBM3D\n#assert_rbm_axioms\n' > pre0.lean; lake env lean pre0.lean; echo exit $?
exit 0
$ printf 'import RBM3D\nimport RBM3D.BA.Step5IIIEdet\n#assert_rbm_axioms\n' > pre.lean; lake env lean pre.lean; echo exit $?
pre.lean:3:0: error: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`, `refutedProps`, `supersededProps`:
  [RBM.BA.BAStep5IIIEMatrix]
Classify each of them: borrowed from the literature, owed by this formalization, a predicate that defines the objects under study, refuted (shown false and superseded), or superseded (not needed).
exit 1
$ git show main:RBM3D/Test/Axioms.lean | grep -n Step5IIIE; echo rc=$?
rc=1
```
So once the hub adds `import RBM3D.BA.Step5IIIEdet` to `RBM3D.lean` (rule (A) 4), the full `lake build` fails (rule (A) 5).
The cause is the ticket, not the proof: the matrix bundle is by design a premise that only U5c concludes (answer (4)), so
some registry classification is needed. `RBM3D/Test/Axioms.lean` is not a sole writable file of this ticket. The prover
reported the same failure and proposed an `owedProps` line (prove (d) 1). A local fix inside the writable file would be a
theorem concluding `BAStep5IIIEMatrix`; the bundle has no cap on `Λ, K₀, J, D` of its own, so such a witness would be
degenerate (it is U5c's composed instance). It is not a repair the repairer should make. **Missing input:** a
dispatcher decision on registering `RBM.BA.BAStep5IIIEMatrix`, e.g. an `owedProps` line (owner U5c, `T2485`), through an
amendment that makes `RBM3D/Test/Axioms.lean` writable or an Approved hub instruction at merge (T2454 precedent, CONTROL :386).

## 6. Paper deltas
- `2ℓ*` cut of `wG`: T2459b; HS route instead of the entrywise one: T2459c. Both are in `T2459-design.md:264-268` and pending
  under `docs/paper-deltas.md:1598` (U5 argument, numbered when the row merges).
- Explicit loss `lossE2wG`: D437. Floor `(L^dW^{6d})² ≤ W^D` instead of `W^D ≥ N`: D429, D434, D513. `M_u = W^d(1-u)`: D376.
- **Not covered:** the scalar bundle's cap `J ≤ W^{1/2}` (paper `lem_dec_calE` has no cap on `J*`; the band had `J ≤ W`,
  D439/D454 recorded that it is unused). It is unused by targets 4-5 here too. Proposed candidate **T2482a** (auditor):
  "`BAStep5IIIEScalar` carries `1 ≤ J ≤ W^{1/2}` (U5c's realized control); targets 4-5 do not read the cap or `0 < lam`".
  The pin is the dispatcher's text, so this does not need a source change. Record it with the merge.

## 7. Observations (no RETURN)
- O1: the probe `RBM3D/Probe/T2482Pins.lean` is on the branch. Under rule (A) 3 the hub brings in only `BA/Step5IIIEdet.lean`
  (and the root import), as in the T2454 precedent.
- O2: prove report (b) line 239 calls the pins "text-equal"; that is confirmed here by elaboration (`rfl`/term equality), §2.
- O3: the 72 declarations include 60 public ones (prove (b): 60 × standard axioms). I re-printed the 10 endpoint/witness theorems.

## Verdict
| target | statement | instance | build/axioms | verdict |
|---|---|---|---|---|
| 1 trace bounds (a)-(c) | = pins | 2×2 matrices | ok | PASS |
| 2 loop HS (Fin, list, glue) | = pins (1a-audit texts) | `H = 0`, `seqHflowBA`, k = 3, 6 | ok | PASS |
| 3 bundle | `rfl` with pins | scalar at n = 1, 800 | ok; **registry fails** | BLOCKED (§5) |
| 4 `lk`, 5 `wG` | = pins | n = 800 (and n = 1), matrix part hypothesis | ok | PASS on content |
| 8 (a) | — | as above | ok | PASS |
**Overall: BLOCKED. Needs dispatcher sign-off.** Every statement, instance and per-module build passes. The merge build
fails on the unregistered premise `RBM.BA.BAStep5IIIEMatrix`, and the fix lies outside the sole writable files (§5).
Items for the dispatcher (not for a repairer):
1. Decide how to classify `RBM.BA.BAStep5IIIEMatrix` in `RBM3D/Test/Axioms.lean` (proposed: `owedProps`, owner U5c/T2485), and
   authorize that edit (amendment or Approved instruction at merge). After that, rerun the pre-check of §5 (expect exit 0).
2. Number paper-delta candidate T2482a (§6) together with T2459b, T2459c when the row merges.
