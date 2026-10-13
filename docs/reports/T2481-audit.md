Auditor model: claude-opus-5-5

# T2481 audit (round 1) — Tue Oct 13 01:28:42 UTC 2026

Branch `t/T2481` at a778b55f (merge-base with main 82deb62b; main 650a122d). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2481-audit1` (detached).
Scratch: scratchpad `T2481/` (`audchk.lean`, `sdiff.py`, `assert.lean`, `assert0.lean`).

## 1. Diff, build, hygiene

```
$ git diff --name-only main...t/T2481
RBM3D/BA/Step5IIIKer.lean
RBM3D/BA/Step5IIIKer2.lean
$ wc -l   ->  709 RBM3D/BA/Step5IIIKer.lean, 471 RBM3D/BA/Step5IIIKer2.lean   (stop line 2,000 per file; no split)
$ lake build RBM3D.BA.Step5IIIKer RBM3D.BA.Step5IIIKer2 ; echo exit $?
exit 0
Build completed successfully (4064 jobs).
(grep -c error build.out -> 0; no warning line names Step5IIIKer*)
$ grep -nE '\bsorry\b|\badmit\b|native_decide|^\s*axiom\b' <two files>          -> exit 1 (no hit)
$ grep -nE '^\s*(structure|class|instance|opaque|axiom)\b' <two files>           -> exit 1 (no hit)
$ grep -n "open private" <two files>                                              -> exit 1 (no hit)
$ C1 grep 1 'BAK_le_small|BAMB_upper_small|BAGbEXPij[^']|Mbound_AO|W\^\(-eps|BAm_im_lower_window'   -> exit 1
$ C1 grep 2 'STGridRepNgL|withLam|\|E\||norm_mE|mSigma|STflowE|etaT|≤ A \*'                         -> exit 1
$ grep -rln "BA.Step5IIIKer" RBM3D RBM3D.lean
RBM3D/BA/Step5IIIKer2.lean          (only importer of Step5IIIKer; RBM3D.lean untouched, hub adds both imports)
$ imports: Step5IIIKer: Chain/Step5Gen, Chain/Step2Kern, BA/{Step2BA,EKPins,KKernel,Prop5Short,Prop6Path,GreenSchur,GreenStab,EMn2BA,TwistStep2}
           Step5IIIKer2: BA/Step5IIIKer           (= ticket layout; no band/U5b import)
```

## 2. Statements against the pins (check file `docs/tickets/checks/T2481-check.lean`)

Script text diff (whitespace-normalised body after `:=` / after the theorem name):
```
$ python3 sdiff.py T2481-check.lean Step5IIIKer.lean Step5IIIKer2.lean
T2481_BAKernel vs BAStep5IIIKernel : IDENTICAL
T2481_BATailSq vs BAStep5IIITailSq : IDENTICAL
T2481_BATailSqQV vs BAStep5IIITailSqQV : IDENTICAL
T2481_KernelAtFlow vs baStep5IIIKernel_at_flow : IDENTICAL
T2481_UKerFar vs baStep5III_uKer_far : IDENTICAL
```
Compiled adapters (check file verbatim + `import RBM3D.BA.Step5IIIKer{,2}`, appended before `end RBM.BA`):
```
example : ∀ d, T2481_BAKernel d := baStep5IIIKernel_holds
example : ∀ d, T2481_BAKernel d = BAStep5IIIKernel d := fun _ => rfl
example : ∀ d, T2481_KernelAtFlow d := baStep5IIIKernel_at_flow
example : ∀ d, T2481_UKerFar d := baStep5III_uKer_far
example : ∀ d, T2481_BATailSq d := baStep5IIITailSq_holds
example : ∀ d, T2481_BATailSq d = BAStep5IIITailSq d := fun _ => rfl
example : ∀ d, T2481_BATailSqQV d := baStep5IIITailSqQV_holds
example : ∀ d, T2481_BATailSqQV d = BAStep5IIITailSqQV d := fun _ => rfl
example : ∀ d, T2481_Lam0LeLam d := fun _ κ _ _ _ hκ _ _ hflow n hpos => baStep5III_lam0_le_lam hκ hflow n hpos
example : ∀ d, T2481_ThetaFar d := fun _ hd _ _ _ _ hκ hε h𝔡 _ _ hflow t ht0 ht D hD =>
  baStep5III_Theta_far hd hκ hε h𝔡 hflow (t := t) ht0 ht (D := D) hD
$ lake env lean audchk.lean ; echo exit $?
exit 0          (no error line; the whole check file, Parts 1-3 and the shape examples, also elaborates on the branch)
```
Mathematical reading (paper `3_5_Loop_Hierarchy.tex:2344-2362`, lemma `TailtoTail`): hypotheses `1-s ≥ 1-t ≥ λ²`
(Lean `0 ≤ s ≤ t < 1`, `sz.lam n ^ 2 ≤ 1 - t`), `|A_b| ≤ T_{s,D}`, conclusion `≲ T_{t,D} + ((1-s)/(1-t))² W^{-D}`; Lean
(`STTailtoTailConclgL`, `Chain/Step5Gen.lean:169`) has `Cc · T_{t,D} + ρ² W^{-D}` (coefficient 1 on the floor: at least as
strong), all four `σ`, every `D`. `Cc` sits after `3 ≤ d, κ, 𝔡` and before `sz, lam0, E, n, D, s, t` (and before `ε 𝔠 sz z` at the
flow): it depends on `(d, 𝔡⁻¹, κ)` only. BA additions `BAReal`, `0 < lam0 n ≤ 𝔡⁻¹`, `lam0 n ≤ sz.lam n` replace `‖m‖ = 1`
(candidate T2481a). Target 4 (b) quantifies all `(τ, τ')`, `0 ≤ v ≤ w ≤ t₀`, `sz.lam² ≤ 1 - w`, beyond `(log W)^{3/2}`, with
the threshold in `n` after `D, 𝔠, sz, z` (`∀ᶠ n`) and before `v w τ τ' x y`: uniform, as the ticket asks. Target 5 / 5-QV:
near cut `2ℓ*`, (H1)-(H3) inline, `Cq` before `sz … Y`, far term `4 Y L^d ρ³ W^{-D₂}`, `4 ≤ log W`: as pinned.

Target 2 (`T2481_BAweighted`) is not in the branch: the 1a chose route (b) for target 3, and dispatcher answer (1) (ticket,
DECISIONS §280 (3)) says "target 2 … is dropped and the report says so". The prove report says so (sections (a), (b)(2), (d)).

## 3. Hidden hypotheses, vacuity, cycles

- New declarations are `def … : Prop` (the three pins), theorems and two instance `def`s (`Step5IIIKer2_Xinst/Yinst`); no
  `structure`, `class`, `instance` (grep above). The public `Prop`s are conclusions proved here (`_holds`), not premises.
- Premises are merged Props only: `BAFlow`, `BAReal` (merged), plus inline (H1)-(H3) of target 5 (the ticket's design; (H3) is
  discharged at the flow by 4 (b), (H1)/(H2) belong to U5b-U5d per dispatcher answer (6)). No unmerged pin is assumed.
- No cycle: the files import only merged modules; Step5IIIKer2 imports Step5IIIKer only.
- Joint satisfiability: every deterministic hypothesis is discharged at `flow_sz0` in the instances (§4).

## 4. Compiled nonempty instances (`d = 3`, `sz0`, `zSeq`, `flow_sz0`, `(κ,ε,𝔠,𝔡) = (1/2,1/10,1/6,1/10)`)

```
$ grep -nE '^example' <two files>
Step5IIIKer.lean:675  target 1   eventually 0 < g₀ ∧ g₀ ≤ sz0.lam   (BAflow_lam0_window, flow_sz0)
Step5IIIKer.lean:681  target 3   ∃ Cc>0, ∀ᶠ n, ∀ D, STTailtoTailConclgL (baFMz sz0 zSeq) n Cc D (1/10) (1/2)
Step5IIIKer.lean:689  target 4a  t ≡ 1/2 (half_lt_t0), D = 1
Step5IIIKer.lean:698  target 4b  v = 1/10, w = 1/2, D = 1, all τ τ'  (half_lt_t0, Step5IIIKer_sz0_reg)
Step5IIIKer2.lean:410 target 5   p = 1, X = Step5IIIKer2_Xinst (= T_{1/10,1}(b)², nonzero, equality in H1), Y = Yinst, D = D₂ = 1;
                                 H1 (Xinst_near), H2 (Xinst_crude), H3 (baStep5III_uKer_far), 4 ≤ log W (W → ∞), BAReal (BAflow_real) discharged
Step5IIIKer2.lean:437 target 5QV composed with 4b: H3 and 4 ≤ log W discharged; H1, H2 stay premises (allowed: U5b/U5c/U5d sources)
```
All six compile (the module build of §1). `BAStep5IIIKernel_holds` (sequence form) is instantiated through `_at_flow`, whose
proof applies it with `lam0 = BAflowLam0`. Nondegeneracy: `L = 4(n+1) ≥ 4`, `W = (2(n+1))^5`, `s < t` / `v < w` strictly inside
`[0, t₀)`, regime `sz0.lam ≤ 1/64` nonempty, far set nonempty for large `n` (`ℓ* = (5 log 2(n+1))^{3/2} < L/2 = 2(n+1)`;
prove report (a)(i): n = 1000, ℓ* = 234.3 vs L/2 = 2002). No `N = 0`, empty index, collapsed window or `False` premise.

## 5. Axioms

```
$ #print axioms (appended to audchk.lean)
'RBM.BA.baStep5III_lam0_le_lam' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5IIIKernel_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5IIIKernel_at_flow' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5III_Theta_far' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5III_uKer_far' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5IIITailSq_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5IIITailSqQV_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean assert.lean    # import RBM3D + both modules + #assert_rbm_axioms ; echo exit $?
exit 0
axiom audit: 14297 theorems, 4503 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ diff (assert0.lean = import RBM3D alone, output from line 2, minus the count line) vs assert.lean | wc -l
0          (no new premise-scan / ledger line: registry none)
```

## 6. Paper deltas

Prove report (d) proposes T2481a (kernel at BA, guarded per-index form for `‖m‖ = 1`; = T2459a), T2481b (near cut `2ℓ*`;
= T2459b), T2481c (Θ far field at mixed charges, 4 (a); = T2459e), T2481d (BA `tailtoTailSq` vs band 7g: cut, (H3) on `uKer`,
`Cq`, BA premises in place of `|E| ≤ 2`), T2481e (4 (b), `uKer` far field uniform in `v ≤ w ≤ t₀`). Every Lean/paper difference
found in §2 is covered (the floor coefficient 1 and the explicit `Cc` are strengthenings inside T2481a). Target 1 is a BA-internal
coupling fact (no paper statement). Numbering at merge (§269 (8)).

## 7. Verdicts

| target | statement | hidden/vacuity | instance | build/axioms | deltas | verdict |
|---|---|---|---|---|---|---|
| 1 `baStep5III_lam0_le_lam` | = pin (binder adapter) | none | :675 | ok | n/a | PASS |
| 2 `BAStep5IIIWeighted` | dropped by dispatcher answer (1) under route (b) | — | — | — | — | n/a (sanctioned drop) |
| 3 `BAStep5IIIKernel`, `_holds`, `_at_flow` | = pins (text + compile) | none | :681 | ok | T2481a | PASS |
| 4 (a) `baStep5III_Theta_far` | = pin (binder adapter) | none | :689 | ok | T2481c | PASS |
| 4 (b) `baStep5III_uKer_far` | = pin (text + compile) | none | :698 | ok | T2481e | PASS |
| 5 `BAStep5IIITailSq`, `_holds`; QV | = pins (text + compile) | H1-H3 inline (ticket) | Ker2:410, :437 | ok | T2481b, d | PASS |
| 6 instances | — | — | all deterministic premises discharged | ok | — | PASS |

## 8. Observations (no RETURN)

- O1. The ticket's acceptance list asks an auditor adapter for target 2; target 2 is dropped by dispatcher answer (1), so none
  is possible. Recorded only.
- O2. 4 (b)'s proof threshold (`2C W^{d+D} ≤ e^{c(log W)^{3/2}}`, `c ≤ 1.29e-32 / 2`) is analytically astronomically late
  (prove report: `log W ≳ 1.5e66` at D = 1); this is an existential `∀ᶠ n` threshold in the statement, not a witness of a
  hypothesis; the prove report's numerics show the bound already at W = 1e3, 1e6. Downstream U5d should not expect a usable
  explicit `n`.
- O3. Public helpers carry the stem `Step5IIIKer_`/`Step5IIIKer2_` (rule (E)), not `private`; allowed.
- O4. Prove report header and (b) are consistent with the files; its axiom-count line (14252) predates later merges on main
  (here 14297 with main's current build cache); immaterial.

**Overall: PASS** (targets 1, 3, 4 (a), 4 (b), 5, 5-QV, 6; target 2 dropped under dispatcher answer (1)). No dispatcher sign-off needed.
