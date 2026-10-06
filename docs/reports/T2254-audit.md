Auditor model: claude-opus-5-5

# T2254 audit (round 1) — LW-14d `Graph/LWExpTerm4`
Written `Tue Oct  6 05:24:23 UTC 2026` (`date -u`). Branch `t/T2254` at `cdf2967`, merge-base `24b85cd`; audit worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2254-audit1` (detached). Scratch: `scratchpad/T2254/`.

## 1. Scope, hygiene
```
$ git diff --stat main...t/T2254
 RBM3D/Graph/LWExpTerm4.lean | 1838 +++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean      |    3 -
$ git diff main...t/T2254 -- RBM3D/Test/Axioms.lean | grep '^-  '      # (cut)
-   `RBM.Gauss.Sizes.LWExpI1K, -- `I₁`, `J₁` ...: LW-14d
-   `RBM.Gauss.Sizes.LWExpI23K, -- `I₂`, `I₃`, `J₂`, `J₃` ...: LW-14d
-   `RBM.Gauss.Sizes.LWExpI41K, -- `I₄₁`, `J₄₁` ...: LW-14d
$ grep -nE '\b(sorry|admit|native_decide)\b|^\s*axiom |^(noncomputable )?(def|abbrev|structure|class|instance|opaque) ' LWExpTerm4.lean
(no output)          # no Prop/def/structure; 5 `private def`s (pad, rho, Pm, R23, Ra: data, not Props)
$ grep -nE '^import' LWExpTerm4.lean
LWExpTerm2, Loop.PureLoop, Defs.RadialSum, Loop.KLUnique, Induction.Step34Pins, Induction.ScaleFacts   # all allowed
$ grep -nE '^(protected )?(theorem|lemma)' LWExpTerm4.lean | grep -vE 'lwExpTerm4_|_holds|lwCutExp_of_G5'
(no output)          # every public name pinned or prefixed; 64 private decls
```
Only the two sole writable files; no merged file or frozen signature touched. Deletions are by text, each `…_holds` unconditional (§3).

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Graph.LWExpTerm4
Build completed successfully (3857 jobs).        # exit 0; only longLine linter notes, no errors
$ lake env lean scratchpad/T2254/audit_check.lean   # exit 0; #print axioms:
'RBM.Gauss.Sizes.lwExpI1K_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpI23K_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpI41K_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwCutExp_of_G5'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpTerm4_kerSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpTerm4_ward2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpTerm4_kward' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpTerm4_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpTerm4_L3' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwExpTerm4_inst_{cut,I1K,I23K,I41K,kerSum,ward2,L3_full,kward,diag}' : [propext, Classical.choice, Quot.sound]  (9 lines, all identical; condensed)
```
Registry pre-check (all 294 root imports of the branch's `RBM3D.lean` + `import RBM3D.Graph.LWExpTerm4` + `#assert_rbm_axioms`,
after `lake build <those modules> RBM3D.Graph.LWExpTerm4` → `Build completed successfully (4056 jobs)`, incl. `Built RBM3D.Test.Axioms`):
```
$ lake env lean scratchpad/T2254/precheck.lean      # exit 0
axiom audit: 7521 theorems, 2530 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
registry: 2 borrowed + 154 owed + 98 structural + 7 refuted + 12 superseded; ...
$ grep -cE 'LWExpI1K|LWExpI23K|LWExpI41K' precheck.out
0
```

## 3. Statements against the pins (check file section 2, copied by `sed` verbatim into a scratch namespace)
`audit_check.lean` = `import RBM3D.Graph.LWExpTerm4` + section 2 of `docs/tickets/checks/T2254-check.lean`
(`sed -n '/^\/-! ## Section 2/,/^def LwCutExpOfG5/p'`) + these term-mode examples (no `by`); exit 0, no errors:
```
example : ∀ d, LWExpI1K d := @lwExpI1K_holds
example : ∀ d, LWExpI23K d := @lwExpI23K_holds
example : ∀ d, LWExpI41K d := @lwExpI41K_holds
example : ∀ d, T2254Check.LwCutExpOfG5'Pin d := @lwCutExp_of_G5'
example : T2254Check.LwExpTerm4KerSumPin := fun d sz K hK => lwExpTerm4_kerSum d sz K hK
example : T2254Check.LwExpTerm4WardPin := fun d sz n E t hE ht s a ω => lwExpTerm4_ward2 d sz n E t hE ht s a ω
example : ∀ d, T2254Check.LwExpTerm4KwardPin d := fun d => lwExpTerm4_kward d
example : ∀ d, T2254Check.LwExpTerm4DiagPin d := fun d => lwExpTerm4_diag d
example : T2254Check.LwExpTerm4L3Pin := fun d sz n E t hE ht σ b c ω A hA => lwExpTerm4_L3 d sz n E t hE ht σ b c ω A hA
```
- Targets 6–8 close the merged pins `LWExpI1K/I23K/I41K` (`LWExpTerm2.lean:81,96,115`) exactly, for every `d`, every
  `LWExpKer` kernel, both charges `s` (the index set of the pins is unchanged; no extra hypothesis). Not a special case.
- Target 9 is `LWExpG5' d → LWCutExp d`, exactly the pin.
- Targets 1–5 are definitionally the pin bodies (accepted by unannotated lambdas). Target 1 carries no `3 ≤ d` (as
  pinned); targets 2, 5 only `|E| < 2`, `t < 1`; targets 3, 4 keep the pin's `3 ≤ d`, `STFlow`, `0 ≤ t ≤ lemT`.

## 4. Hidden hypotheses, vacuity, cycles
- The file defines no `Prop`, no structure; hypotheses are those of the pins only. Dependencies are merged modules
  (imports above); the new file is imported by nothing (`grep` of new names outside the file: 0, per §1 and prove report).
- `LWExpKer` is satisfiable: `lwExpTerm2_inst_ker_KK` (merged) is consumed by `lwExpTerm4_inst_kerSum` without hypotheses.
- No external hypothesis is introduced; the ST/LW laws in the instances are other gates' owed pins (registry above).

## 5. Compiled nonempty instances (`d = 3`, `sz0` (`L 0 = 4`, `W 0 = 32`), `z0`, `flow_z0`, `tInst`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`)
`#check` output of `audit_check.lean` (abbreviated: `sz0`, `z0`, `tInst`, `E n := STflowE z0 n`):
```
lwExpTerm4_inst_cut    : LWExpG5' 3 → STLocalEntry → LWAvgLaw → STLmax → STLK → STDecay → sz0.Prec (‖∫ LWE …‖) ((1-tInst n)⁻¹ * Bctl^(5/2))
lwExpTerm4_inst_I1K    : LWAvgLaw → STLK → sz0.Prec (‖∑ a₁, lwExpTerm2_KK … a₁ (p.2 1) * ∫ …‖) (Bctl^3)
lwExpTerm4_inst_I23K   : STLocalEntry → LWAvgLaw → STLmax → STLK → STDecay → sz0.Prec (…) (etaT⁻¹ * Bctl^(5/2))
lwExpTerm4_inst_I41K   : LWAvgLaw → STLmax → STLK → sz0.Prec (…) (etaT⁻¹ * Bctl^3)
lwExpTerm4_inst_kerSum : ∃ C, 0 < C ∧ ∀ n b, ∑ a ‖lwExpTerm2_KK … a b‖ ≤ C ∧ ∑ a ‖lwExpTerm2_KK … b a‖ ≤ C
lwExpTerm4_inst_ward2  : ∀ (s : Bool) (a : Zd 3 (sz0.L 0)) ω, W 0^3 * ∑ b ‖Lloop … ![s,true] ![a,b] ω‖ ≤ etaT⁻¹ * ‖Lloop … ![true] ![a] ω‖
lwExpTerm4_inst_L3_full: ∀ σ b c ω, W 0^3 * ∑ a ‖Lloop … ![true,true,σ] ![a,b,c] ω‖ ≤ etaT⁻¹ * etaT⁻¹ * √(STmaxLoop2 …)
lwExpTerm4_inst_kward  : sz0.Prec (W n^3 * ∑ a ‖STKloop … ![p.1,true] ![a,p.2]‖) (etaT⁻¹)
lwExpTerm4_inst_diag   : STLocalEntry → sz0.Prec (‖Gt … x x‖) 1
```
Every deterministic hypothesis (`3 ≤ 3`, positivity of `1/10`, `STFlow` via `flow_z0`, `0 ≤ tInst ≤ lemT`, `|E| < 2` via
`st6_flowE_lt_two`, `t < 1` via `st5_t_lt_one`, `LWExpKer` via `lwExpTerm2_inst_ker_KK`) is discharged; remaining
hypotheses are only `LWExpG5'` (LW-14c) and owed ST/LW laws, as the ticket allows (instance (1) "only `LWExpG5' 3` and
the five ST laws"). Targets 2, 5 instantiated at `n = 0` (`L = 4`, `W = 32`, nonempty index), target 5 with `A`
discharged (`A = η⁻¹`, `inst_L3_full` has no hypothesis). Target 9 instance = `inst_cut`. No `N = 0`, empty index,
collapsed window or `False` premise; witnesses are the standard `sz0` data, not astronomically large.

## 6. Paper deltas
Lean/paper differences and their coverage (prove report (d), temporary tags):
- `B:43-49` (`eq:termI2`): vertex Ward + `max|G_xx| ≺ 1` (`STLocalEntry`) + `STLmax` instead of the entrywise law → `T2254a`.
- `B:14` "`σ = +` analogous" for `I₄₁`, `(+,+)` 2-loops not positive, AM-GM to `(-,+)` → `T2254b` (refines T2243b).
- `B:34` "`J_i` the same way": kernel column sum `≤ C` replaces `Σ S^{(B)} = 1` → `T2254c` (refines T2243a; D561 in `docs/paper-deltas.md:1520`).
Every statement difference of the five new theorems against the paper is one of these three; coverage complete.

## 7. Verdicts
| target | verdict |
|---|---|
| 1 `lwExpTerm4_kerSum` | PASS |
| 2 `lwExpTerm4_ward2` | PASS |
| 3 `lwExpTerm4_kward` | PASS |
| 4 `lwExpTerm4_diag` | PASS |
| 5 `lwExpTerm4_L3` | PASS |
| 6 `lwExpI1K_holds` | PASS |
| 7 `lwExpI23K_holds` | PASS |
| 8 `lwExpI41K_holds` (both `s`) | PASS |
| 9 `lwCutExp_of_G5'` | PASS |
| 10 instances (1)–(4) | PASS |
| registry (`Test/Axioms.lean`, 3 deletions) | PASS |

**Overall: PASS.** No dispatcher sign-off needed.

## 8. Observations (no RETURN)
- O1 (ticket text): the ticket's suggested product bound `Σ_{x∈Z^d} e^{-c|x|_∞} ≤ (Σ_y e^{-c|y|})^d` is the wrong direction
  (`|x|_∞ ≤ |x|_1`); prove report (a) gives `10.13 < 49.98`. The file does not use it (padding + `zdistD ≤ d·zdistInf`).
  Dispatcher may want to correct the ticket template / `T2243` (a) wording.
- O2 (merge): the registry deletion and the root import `import RBM3D.Graph.LWExpTerm4` must land in the same merge
  commit (otherwise `#assert_rbm_axioms` sees the three premises unregistered). `Test/Axioms.lean` on `main` gained one
  line (T2252, `8aa37bf`) since the merge-base; apply the 3-line deletion by text.
- O3 (report): stage-1a size estimate (vi) was "not given"; file is 1838 lines vs estimate 1300–1500. Process only.
