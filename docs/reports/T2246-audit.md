Auditor model: claude-opus-5-5
# T2246 audit (S3-12c1, round 1) — Tue Oct  6 04:19:46 UTC 2026
Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2246-audit1`, detached at `t/T2246` = 8c1a9b5 (merge-base b35643d; main 9403c24).
Scratch: `$S` = `<scratchpad>/T2246` (`AuditCheck.lean`, `Reg.lean`, `build.log`, `reg.out`).

## 1. Scope and hygiene
```
$ git diff --stat main...t/T2246
 RBM3D/Induction/NQEndFlow.lean | 1095 ++++   RBM3D/Test/Axioms.lean | 19 +-   (2 files)
$ grep -nE "sorry|admit|native_decide|^axiom|maxHeartbeats" RBM3D/Induction/NQEndFlow.lean
(no output)
$ git merge-tree --write-tree --name-only main t/T2246      # exit 0, no conflict list
ddf4dcede6b704fc739a73ee64cb993176d08d7c
```
Only the two sole writable files; no merged file touched; no `maxHeartbeats` override.

## 2. Build and axioms
```
$ lake build RBM3D.Induction.NQEndFlow
ℹ [3845/3845] Built RBM3D.Induction.NQEndFlow (6.0s)
info: NQEndFlow.lean:1078..1095: 18 × '...' depends on axioms: [propext, Classical.choice, Quot.sound]
  (STNQConcl'', STXiBoot', STNQConclPT'', STOeqNQ'', STOeqQt', STOeqQtNZ', STIterR', STIterations', STIterationsII',
   STOeqNQPT'', nqFlowLam, nqFlowPhiC, stXiBoot'_of_stXiBoot, stOeqNQ''_of_stOeqNQ', stOeqQt'_of_stOeqQt,
   stOeqQtNZ'_of_stOeqQtNZ, stOeqNQPT''_holds, NQEndFlowInst.inst_OeqNQPT'')
Build completed successfully (3845 jobs).     exit 0
$ grep -n "NQEndFlow.lean.*\(warning\|error\)" $S/build.log
(no output)
```

## 3. Statements against the check file (target 1: ten pins + vocabulary)
Text diff (body extracted by awk from `docs/tickets/checks/T2246-check.lean` §2 and the new file):
```
== STNQConcl''   1c1 < def STNQConcl'' {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
                     > def STNQConcl'' (E s t : ℕ → ℝ) : Prop :=
== STXiBoot'     1c1 (same header-only hunk)        == STNQConclPT''  1c1 (same header-only hunk)
== STOeqNQ'' / STOeqQt' / STOeqQtNZ' / STIterR' / STIterations' / STIterationsII' / STOeqNQPT'' / nqFlowLam / nqFlowPhiC:
   no diff (nqFlowPhiC: only the trailing check-file comment line differs)
```
The header hunks are the `section Pins` binder `variable {d : ℕ} (sz : Sizes d)` (file :72-74), exactly as check §2 allows.
Definitional identity and pinned statements, compiled (`$S/AuditCheck.lean` = `import RBM3D.Induction.NQEndFlow` + the
whole check file + the lines below):
```
example : @_root_.RBM.Gauss.Sizes.STNQConcl'' = @STNQConcl'' := rfl      -- and likewise for all ten pins,
example : @_root_.RBM.Ind.nqFlowLam = @nqFlowLam := rfl                  -- nqFlowLam, nqFlowPhiC (12 rfl lines)
example : T2246_stOeqNQ''_of_stOeqNQ' := @_root_.RBM.Gauss.Sizes.stOeqNQ''_of_stOeqNQ'
example : T2246_stXiBoot'_of_stXiBoot := @_root_.RBM.Gauss.Sizes.stXiBoot'_of_stXiBoot
example : T2246_stOeqQt'_of_stOeqQt := @_root_.RBM.Gauss.Sizes.stOeqQt'_of_stOeqQt
example : T2246_stOeqQtNZ'_of_stOeqQtNZ := @_root_.RBM.Gauss.Sizes.stOeqQtNZ'_of_stOeqQtNZ
example : T2246_stOeqNQPT''_holds := @_root_.RBM.Ind.stOeqNQPT''_holds
$ lake env lean $S/AuditCheck.lean; echo exit $?      →  exit 0, 0 lines containing "error"
'RBM.Ind.stOeqNQPT''_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```
The private bridge's pinned type is checked in-file (NQEndFlow.lean:282, `example : ∀ {d} (sz) (E s t), (∀ n, t n < 1) →
STNQConcl' sz E s t → STNQConcl'' sz E s t := @stNQConcl''_of_stNQConcl'`), compiled in §2's build.

R2* one-token hunks against the merged originals (awk extraction, `def <name>` normalised):
```
== STNQConcl' (Step34PinsP) -> STNQConcl''
<   STbootRHS 2 (fun m => XL m n (q.1 : ℝ)) (fun m => XLK m n (q.1 : ℝ)) (sz.Bctl n (q.1 : ℝ)) n_ p)
>   STbootRHS 2 (fun m => XL m n (q.1 : ℝ)) (fun m => XLK m n (q.1 : ℝ)) (sz.Bctl n (s n)) n_ p)
== STXiBoot (Step34Pins) -> STXiBoot'
<   (fun n q _ => STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n q.1.2) n_ p)
>   (fun n q _ => STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p)
== STIterR (Step34Pins) -> STIterR'
<           STXiBoot sz (STflowE z) s t →
>           STXiBoot' sz (STflowE z) s t →
== STNQConcl'' -> STNQConclPT''
<     Prec sz (U := fun n => TimeIcc s t n × {σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)} ×
>     PrecPT sz (U := fun n => TimeIcc s t n × {σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)} ×
STOeqNQ''/STOeqQt'/STOeqQtNZ'/STIterations'/STIterationsII'/STOeqNQPT'' (:124-155) are the merged one-liners
(Step34PinsP:70, Step34Pins:462,465,497,500) with the primed conclusion/setting only.
```
The `B_u^{1/6}·XLK` term and the `/B_u^{n_}` normalisation are unchanged; only the `STbootRHS` `B` argument moves to `B_s`.
Quantifier order (`𝔠d` before the flow/`s,t`, fixed `n_ p XL XLK` before `≺`) is the merged `STIngR` order.

## 4. Vacuity, hidden hypotheses, cycles
- `stOeqNQPT''_holds : ∀ d, STOeqNQPT'' d` is a closed theorem (no extra binders; `#check` above). Its proof
  (:921-958) uses only merged `gridGoodN_holds`, `nqLinGood_holds`, `v3_premises_of_stFlow`, `st_window`,
  `st_conStInd_sub`, `perTimeDomAt_iff_forall_section` and private `nqFlow_*` helpers; no structure-field hypotheses.
  `𝔠d = min (min 𝔠G 𝔠L) (1/(2d))`, `d·𝔠d ≤ 1/2 < 1` (:932-945), as Design.
- Bridges: monotonicity only (`B_s ≤ B_u` via `STBctl_mono`, `0 < B_s` via `st_Bctl_pos`, `nqFlow_bootRHS_anti`);
  the hypothesis `∀ n, t n < 1` is the pinned one.
- No new external hypothesis. No cycle: no new name is used by a merged file (new module, not imported by anything).
- Registry pre-check (case A: T2245 = 05e5052 is merged on main, `supersededProps` exists):
```
$ printf 'import RBM3D\nimport RBM3D.Induction.NQEndFlow\n#assert_rbm_axioms\n' > $S/Reg.lean
$ lake env lean $S/Reg.lean; echo exit $?       (after lake build RBM3D RBM3D.Test.Axioms in the worktree)
exit 0
axiom audit: 7175 theorems, 2418 definitions, 0 axioms in `RBM` ...
  RBM.Gauss.Sizes.STIterR: 1   RBM.Gauss.Sizes.STOeqNQ: 2   RBM.Gauss.Sizes.STXiBoot: 4
  RBM.Gauss.Sizes.STOeqNQ'': 1  STXiBoot': 1  STOeqQt': 1  STOeqQtNZ': 1  STIterR': 0  STIterations': 0  STIterationsII': 0
premises found by scanning: 144 (borrowed 1, owed 94, structural 33, refuted 6, superseded 10).
```
  Registry diff: seven primes added to `owedProps`; `STOeqNQ'`, `STOeqQt`, `STOeqQtNZ`, `STIterations`,
  `STIterationsII` moved from `owedProps` to `supersededProps` with the case-A comment; `STOeqNQ`, `STXiBoot`, `STIterR`
  kept. Matches the ticket's case A exactly.

## 5. Compiled nonempty instances (file :966-1072, compiled in §2's build)
| Endpoint | Instance | Data / discharged | Remaining hypotheses |
|---|---|---|---|
| `stOeqNQPT''_holds` | `inst_OeqNQPT''` (:974) and the applied `example` (:984) | `sz0` (d=3, L=4(n+1), W=(2(n+1))^5), `z0`, `flow_z0`, s≡0, t≡1/16, `sz0_caseI`, `sz0_con`, C_d=1; `STKbound`/`STKward` from the flow; n_=3, p=1, XL≡XLK≡1 | `STLK s`, `STStep2Concl`, pair hyps `Ξ̂ ≺ 1` (other gates' pins) |
| `stOeqNQ''_of_stOeqNQ'` | :1005, :1011 | same data via `inst_ing` | `STOeqNQ 3` (owed pin), stochastic premises |
| `stNQConcl''_of_stNQConcl'` (private) | :1021 | `t n < 1` by `norm_num` | `STNQConcl'` |
| `stXiBoot'_of_stXiBoot` | :1026 | `t n < 1` discharged | `STXiBoot` (owed) |
| `stOeqQt'_of_stOeqQt` | :1030 | case (i) data via `inst_ing` | `STOeqQt 3` (owed) |
| `stOeqQtNZ'_of_stOeqQtNZ` | :1036 | case (ii) data `szB, zB, 15/16, 31/32`, `szB_caseII`, `conStInd_const` | `STOeqQtNZ 3` (owed) |
| vocabulary (4) | :1046-1061 | `nqFlowLam 1 (1/2) 3 1 = 2^{1/2}`; sqrt = first `STbootRHS` summand; antitone at 1/4 ≤ 1/2; `nqFlowPhiC = 8` | none |
No `N = 0`, empty index, collapsed window (`s < t` at every n) or `False` premise; every deterministic hypothesis is
discharged. Remaining hypotheses are owed stochastic pins of other gates, as CLAUDE.md §4 step 2 permits.

## 6. Paper deltas
Prove report (d) proposes `T2246a` (R2*: martingale summand of `(am;asoiuw)` `3_5:1143-1148` / `(am;asoi222)` `3_5:1366`
at `B_{s,0}`, with T2207d to be numbered at this merge), `T2246b` (window `[s, v]` re-instantiation), `T2246c` (crude
level `nqFlowPhiC`). These cover every Lean/paper statement difference found in §3 (the `B_s` hunk) and the two
proof devices. `STNQConclPT''` (per-time form, DECISIONS §7) is the pinned per-time vocabulary, lifted by S3-12c2.

## 7. Observations (no verdict impact)
- The branch base is b35643d; `RBM3D/Test/Axioms.lean` changed on main since (other tickets' lines). `git merge-tree`
  reports no conflict; the hub should merge the registry hunks, not overwrite the file with the branch copy.
- `STIterR'`, `STIterations'`, `STIterationsII'` currently carry 0 theorems (registered, owed to S3-24b), as intended.

## Verdict
| Target | Verdict |
|---|---|
| 1. ten pins + `nqFlowLam`, `nqFlowPhiC` | PASS |
| 2. bridges (`stNQConcl''_of_stNQConcl'` private, four public) | PASS |
| 3-5. window facts, levels, per-section endpoint (private) | PASS (checked through target 6) |
| 6. `stOeqNQPT''_holds : ∀ d, STOeqNQPT'' d` | PASS |
| Registry (case A) | PASS |
Overall: **PASS**. No dispatcher sign-off needed.
