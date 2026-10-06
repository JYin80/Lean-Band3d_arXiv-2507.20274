Auditor model: claude-opus-5-5
# T2292 audit (round 1): S3-22b `Induction/QtNonzeroFlow`, `stOeqNZPT''_holds`
Written Tue Oct  6 12:51:05 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2292-audit1`,
detached at `t/T2292` = `edf0117` (merge base with `main`: `fbec579`; `main` HEAD `1ba63a2`).
Targets: pins `RBM.Gauss.Sizes.STNZConclPT''`, `RBM.Gauss.Sizes.STOeqNZPT''`; endpoint `RBM.Ind.stOeqNZPT''_holds`.

## 1. Scope and hygiene
```
$ git diff --name-only main...t/T2292
RBM3D/Induction/QtNonzeroFlow.lean
$ wc -l RBM3D/Induction/QtNonzeroFlow.lean ; grep -c ^example ; grep -c ^private
989 / 10 / 30
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom|maxHeartbeats" RBM3D/Induction/QtNonzeroFlow.lean | wc -l
0
$ grep -nE "^(theorem|def|lemma|abbrev)" RBM3D/Induction/QtNonzeroFlow.lean
75:def STNZConclPT'' (E s t : ℕ → ℝ) : Prop :=
95:def STOeqNZPT'' (d : ℕ) : Prop := STIngR d STCaseII (fun sz E s t => STNZConclPT'' sz E s t)
837:theorem stOeqNZPT''_holds : ∀ d : ℕ, STOeqNZPT'' d := by
882:theorem inst_OeqNZPT'' :
$ grep ^import  -> QtNonzeroEnd, NQEndFlow, GridGoodN, NQLin, ScaleFacts3, ZeroModeCalc, Step2Events, Green.Pins
  (no `import RBM3D`, no `NQEndFlowLift`)
$ git grep -n -F <name> main -- RBM3D RBM3D.lean | wc -l
STNZConclPT'': 0  STOeqNZPT'': 0  stOeqNZPT''_holds: 0  inst_OeqNZPT'': 0  QtNonzeroFlowInst: 0  nzFlow_: 0
```
Only the sole writable file is touched; `Test/Axioms.lean` and every merged file unchanged (no frozen signature touched).
All 30 helpers are `private` with prefix `nzFlow_`.

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Induction.QtNonzeroFlow
ℹ [3851/3851] Built RBM3D.Induction.QtNonzeroFlow (5.8s)
info: QtNonzeroFlow.lean:986:0: 'RBM.Gauss.Sizes.STNZConclPT''' depends on axioms: [propext, Classical.choice, Quot.sound]
info: QtNonzeroFlow.lean:987:0: 'RBM.Gauss.Sizes.STOeqNZPT''' depends on axioms: [propext, Classical.choice, Quot.sound]
info: QtNonzeroFlow.lean:988:0: 'RBM.Ind.stOeqNZPT''_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: QtNonzeroFlow.lean:989:0: 'RBM.Ind.QtNonzeroFlowInst.inst_OeqNZPT''' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3851 jobs).   exit=0
$ grep "QtNonzeroFlow.lean" build.log | grep -ci "warning\|error"
0
$ lake build RBM3D   (branch root, without the new import)   exit=0
info: RBM3D.lean:334:0: axiom audit: 8371 theorems, 2784 definitions, 0 axioms in `RBM` ...
$ registry pre-check: lake env lean {import RBM3D [+ import RBM3D.Induction.QtNonzeroFlow]; #assert_rbm_axioms}
before exit=0  axiom audit: 8371 theorems, 2784 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
after  exit=0  axiom audit: 8373 theorems, 2786 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
ledger diff after line 1: empty
```
+2 theorems / +2 definitions = the four public declarations; no new unregistered premise (§20); registry change: none, as the ticket expects.

## 3. Statement against the pin (check file §2, §3)
```
$ diff <(check §2 STNZConclPT'' body, binder `{d : ℕ} (sz : Sizes d)` moved to `section Pins` variable) <(QtNonzeroFlow.lean:75-89)
IDENTICAL
$ grep -n "^def STOeqNZPT''" check file / branch file
210:def STOeqNZPT'' (d : ℕ) : Prop := STIngR d STCaseII (fun sz E s t => STNZConclPT'' sz E s t)
95:def STOeqNZPT'' (d : ℕ) : Prop := STIngR d STCaseII (fun sz E s t => STNZConclPT'' sz E s t)
$ diff <(NQEndFlow.lean STNQConclPT'') <(QtNonzeroFlow.lean:75-89)     # allowed hunks: name, index set, quantity
1c1
< def STNQConclPT'' (E s t : ℕ → ℝ) : Prop :=
> def STNZConclPT'' (E s t : ℕ → ℝ) : Prop :=
8c8
<     PrecPT sz (U := fun n => TimeIcc s t n × {σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)} ×
>     PrecPT sz (U := fun n => TimeIcc s t n × {σA : (Fin n_ → Bool) × Finset (Fin n_) // STIdiff σA.1 ⊆ σA.2} ×
10c10,12
<       (fun n q ω => ‖Lloop sz n (E n) (q.1 : ℝ) q.2.1.1 q.2.2 ω - STKloop sz n (E n) (q.1 : ℝ) q.2.1.1 q.2.2‖ /
>       (fun n q ω => ‖zeroModeSet d (sz.L n) q.2.1.1.2
>           (fun b : Fin n_ → Zd d (sz.L n) =>
>             Lloop sz n (E n) (q.1 : ℝ) q.2.1.1.1 b ω - STKloop sz n (E n) (q.1 : ℝ) q.2.1.1.1 b) q.2.2‖ /
```
(The remaining `14d15` hunk is the trailing blank line of the `sed` extraction.) Statement script (scratch file: the check
file's `namespace RBM.Gauss.Sizes.T2292Check` block verbatim, then):
```
example : @STNZConclPT'' = @RBM.Gauss.Sizes.STNZConclPT'' := rfl
example : STOeqNZPT'' = RBM.Gauss.Sizes.STOeqNZPT'' := rfl
example : RBM.Gauss.Sizes.T2292Check.T2292_stOeqNZPT''_holds := @RBM.Ind.stOeqNZPT''_holds
#check @RBM.Ind.stOeqNZPT''_holds
$ lake env lean stmt.lean
RBM.Ind.stOeqNZPT''_holds : ∀ (d : ℕ), RBM.Gauss.Sizes.STOeqNZPT'' d
'RBM.Ind.stOeqNZPT''_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```
Mathematics (paper `3_5:1561-1572`, proof `:1889-1933`, `(am;asoiuw_smalleta)` `:1914-1919`, "each fixed `u`" `:1931`):
the regime `STCaseII s t := ∀ n, 1 - s n ≤ lam² / L²` is the lemma's `1 − s ≤ ilambda²/L²`; the setting is the merged
`STIngR` (flow, `0 ≤ s < t ≤ lemT`, `STKbound`, `STKward`, `STLK s`, `STConStInd 𝔠d`, `STStep2Concl`), quantifier order
`d → κ ε 𝔡 Cd → ∃ 𝔠d → ∀ 𝔠 sz z …` unchanged; every `n_ ≥ 2`, `p ≥ 1`; index set every `σ`, every `A ⊇ I_diff(σ)`,
every label `a`, every `u ∈ [s,t]` (per time, `PrecPT`); normalisation `/B_u^{n_}`. Differences from the paper: controls
at `u` instead of `sup_u` (stronger); `B_u^{1/6}` instead of `B_t^{1/6}` (stronger, `B_u ≤ B_t`); first summand of
`STbootRHS` at `B_s` (R2*, DECISIONS §80; weaker than `B_t` by `≤ N^{0.70/(4p)}` per the ticket's G1); per-time form
only (the uniform lift is T2292b). All are covered by the candidates below. **Statement: PASS.**

## 4. Hidden hypotheses, vacuity, cycles
- The pins are plain `Prop` definitions with explicit binders; no structure, no class field carries a hypothesis.
- `stOeqNZPT''_holds` has no hypothesis beyond the pinned type (§3 statement script).
- Proof (`:837-862`) uses only merged results: `gridGoodN_holds`, `nqLinGood_holds`, `v3_premises_of_stFlow`,
  `st_conStInd_sub`, `perTimeDomAt_iff_forall_section`, and the private `nzFlow_section`/`nzFlow_core` (which call the
  merged `nzGridEndN`). No import of `RBM3D`, `NQEndFlowLift`, or any unmerged module: no cycle.
- `𝔠d := min 𝔠G 𝔠L` with `0 < 𝔠d ≤ 𝔠G ≤ 1/100`, as in the Design. The conclusion is not vacuous: its parameter type is
  nonempty (instance (4)), and the `STIngR` setting has a compiled witness (instance (1)).
- No new external hypothesis (the stochastic premises are those of the merged `STIngR`), so no new limit check is owed.
**PASS.**

## 5. Compiled nonempty instances (namespace `RBM.Ind.QtNonzeroFlowInst`, `:874-980`; all compile, §2)
Data: case-(ii) data of the merged `inst_OeqQtNZ`: `szB` (`d = 3`, `L = 4`, `W = n + 4`, `lam = 1`), flow `zB`
(`flow_zB` at `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`), `s ≡ 15/16`, `t ≡ 31/32`, `C_d = 1`.
- (1) `inst_OeqNZPT''` (`:882`) = `inst_ing STCaseII … (stOeqNZPT''_holds 3) szB zB flow_zB …`: discharges `0 ≤ s`,
  `s < t` (`norm_num`), `t ≤ lemT` (`szB_flow_ht`), `STCaseII` (`szB_caseII`: `1 − 15/16 = 1/16 = 1²/4²`),
  `STConStInd 𝔠d` for every `𝔠d > 0` (`conStInd_const`), `0 < C_d`. The merged `InstIngConcl` leaves exactly
  `STKbound`, `STKward`, `STLK s`, `STStep2Concl` as premises (`Step34Pins.lean:863-867`).
- (2) `:894`: the applied conclusion at `n_ = 3`, `p = 1`, `XL ≡ XLK ≡ 1`, with `STKbound`/`STKward` discharged by
  `stKbound_of_flow`/`stKward_of_flow`; remaining hypotheses `STLK s`, `STStep2Concl`, the pair hypotheses `Ξ̂ ≺ 1`
  are other gates' pins (allowed by CLAUDE.md §4 step 2). Conclusion for every `σ`, every `A ⊇ I_diff σ`, every `a`.
- (3) `nzFlow_initQ` at `szB`, `k = 3`, `ε = 1/160`, `D = 3` (`:919`) and at one size index (`:929`, `.exists`);
  `nzFlow_collapsed` at `sig3`, `A = {0,1}` (`:941`); `(normQA2)` numeric (`:952`); measurability (`:958`).
- (4) `:966` the pin's parameter type is `Nonempty` at every `n` (member `(15/16, (sig3, {0,1}), 0)`); `:970` the
  member `(const +, ∅)`; `:974` `STIdiff sig3 = {0, 1}`.
- (5) `:978` `example : ∀ d : ℕ, STOeqNZPT'' d := @stOeqNZPT''_holds`, and the check-file `example` (§3) compiles.
No `N = 0` (`N = (4(n+4))^3`), no empty index, window `[15/16, 31/32]` not collapsed, no `False` premise, no astronomical
witness. **PASS.**

## 6. Paper deltas
`grep -n T2292 docs/paper-deltas.md` → no hits (not yet appended). The prove report (d) proposes `T2292a` (per-time
case-(ii) projected endpoint, every `σ`, `A ⊇ I_diff(σ)`, R2* first summand at `B_s`, controls at `u`, uniform form in
T2292b), `T2292c` (projected initial assumption from `STLK s` + `(normQA2)` at half the loss), `T2292d` (collapsed
sections `u_n = s_n`), `T2292e` (restriction of `STStep2Concl` and pair hypotheses to `[s, v]` per section), `T2292f`
(crude level `Φc = nqFlowPhiC`). Letter `b` skipped as the ticket requires. Every difference listed in §3 is covered
(`B_u^{1/6}` vs `B_t^{1/6}` and controls at `u` vs `sup_u` are inside `T2292a`'s "controls taken at the endpoint `u`").
**PASS.**

## 7. Observations (no RETURN)
- O1: the prove report's script directory (`$SCR`) is the same scratchpad path this audit used; the audit's own
  outputs above were produced fresh in the audit worktree and do not rely on any prover file.
- O2: `T2292a` names "controls at `u`" but does not state `B_u^{1/6}` vs the paper's `B_{t}^{1/6}` in so many words;
  the dispatcher may add that clause when numbering (both are strengthenings).

## Verdict
| target | verdict |
|---|---|
| `RBM.Gauss.Sizes.STNZConclPT''` (pin) | PASS |
| `RBM.Gauss.Sizes.STOeqNZPT''` (pin) | PASS |
| `RBM.Ind.stOeqNZPT''_holds` (endpoint) | PASS |

T2292: **PASS**. No dispatcher sign-off needed.
