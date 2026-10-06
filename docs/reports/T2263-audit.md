Auditor model: claude-opus-5-5

# T2263 audit (S3-15b, `Induction/QDriftB.lean`), round 1 — Tue Oct  6 07:02:46 UTC 2026

Branch `t/T2263` at `f812c4d`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2263-audit1` (detached, fresh).
Pins: `docs/tickets/checks/T2263-check.lean` §3 (`RBM.Ind.T2263Check.T2263_*`).

## 1. Scope
```
$ git diff --name-only main...t/T2263
RBM3D/Induction/QDriftB.lean
$ grep -nE "sorry|admit|native_decide|^axiom|maxHeartbeats|implemented_by|extern|unsafe" RBM3D/Induction/QDriftB.lean; echo "grep exit=$?"
grep exit=1
$ git show t/T2263:RBM3D/Induction/QDriftB.lean | grep -cE "STXiLK|STsupXiLK|STNQConcl|STXiBoot|goodExitTauN|STAlternating|NQEndFlow"
0
```
Only the sole writable file; `RBM3D/Test/Axioms.lean` untouched (none expected). No frozen signature touched (new file only).
Public declarations (grep `^theorem|def|structure|…`): five targets (lines 152, 172, 278, 330, 379) and five
instances in `QDriftBInst` (760, 781, 804, 828, 878); no new `def`/`structure`; every other declaration `private`.

## 2. Build (audit worktree)
```
$ lake build RBM3D.Induction.QDriftB ; echo exit=$?      # error lines / QDriftB lines only
Build completed successfully (3856 jobs).
exit=0
```
(Warnings printed come from upstream merged modules only: `Path/Walk`, `Path/Markov`, `Defs/Tail`, … .)

## 3. Statements against the pins, and axioms
Script: the check file verbatim + `import RBM3D.Induction.QDriftB`, followed by
```
example : RBM.Ind.T2263Check.T2263_drift13_fastDecay := @RBM.Ind.drift13_fastDecay
example : RBM.Ind.T2263Check.T2263_altB4N_fastDecay := @RBM.Ind.altB4N_fastDecay
example : RBM.Ind.T2263Check.T2263_altB5N_fastDecay_moll := @RBM.Ind.altB5N_fastDecay_moll
example : RBM.Ind.T2263Check.T2263_dFlowQN_clsQN := @RBM.Ind.dFlowQN_clsQN
example : RBM.Ind.T2263Check.T2263_alt_hDclsQN := @RBM.Ind.alt_hDclsQN
#print axioms (five targets, five instances)
```
```
$ lake env lean stmt.lean 2>&1 | grep -v "^warning" | grep -E "error|axioms"; echo exit=$?
'RBM.Ind.drift13_fastDecay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.altB4N_fastDecay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.altB5N_fastDecay_moll' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.dFlowQN_clsQN' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.alt_hDclsQN' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QDriftBInst.drift13_fastDecay_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QDriftBInst.altB4N_fastDecay_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QDriftBInst.altB5N_fastDecay_moll_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QDriftBInst.dFlowQN_clsQN_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QDriftBInst.alt_hDclsQN_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```
No `error` line: all five targets have exactly the pinned types (elaborated against the pins).

Registry pre-check:
```
$ printf 'import RBM3D\nimport RBM3D.Induction.QDriftB\n#assert_rbm_axioms\n' > registry.lean; lake env lean registry.lean; echo exit=$?
axiom audit: 7757 theorems, 2576 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
non-vacuity certificates: 0 of 159 premises in the two ledgers; ...
exit=0
```

## 4. Pins against the ticket's mathematics (Design (a)–(f))
- T2 `drift13_fastDecay`: hypotheses `dW^{τ'} ≤ W^{ε'}` and `H ∈ GoodSetN … (m+1) Γ Λ Φ τ' D'`; conclusion
  `EKFastDecay … ε' D'` of `driftTensorN` (= the `ℬ₁₋₃` block of `dFlowQN`, check-file §4 `rfl` shape). No threshold,
  as Design (b). `3 ≤ d` unused but allowed (§36).
- T3 `altB4N_fastDecay`: fixed `(d m Λg K C c C₀ ε' D')` before `∃ W₀`, then `∀ sz n E u H ϑ σ`; hypotheses
  `|E| ≤ 2`, `0 < λ ≤ Λg`, `W₀ ≤ W`, `L^d ≤ W^K`, `0 ≤ u < 1`, `(1−u)⁻¹ ≤ W^K`, `STMollifierProps λ C c ϑ`,
  `‖STLKM‖ ≤ W^{C₀}`; conclusion at arbitrary `(ε', D')`, general `ϑ`. Matches Design (c) (crude sup only, no decay input).
- T4 `altB5N_fastDecay_moll`: same order; explicit mollifier `QopAlgebra_mollifier d L m λ`; Design (d).
  Specialisation to the explicit mollifier is the ticket's design and is covered by D556 (T2239a) / D565 (T2249a).
- T5 `dFlowQN_clsQN`: threshold `QDriftA_W0 d m K C c C₀ ε' D'` (the merged one, Design (a)); index shift as the
  hypothesis `ℓ_u ≤ ℓ_{uu i}` (Design (e)); `ℬ₄`, `ℬ₅` decays as hypotheses (general `ϑ`, Design (d) last sentence);
  conclusion `altClsQN … ε' Dc uu i (4W^{-D'}) (dFlowQN …)`, `δD = 4W^{-D'}` as pinned.
- T6 `alt_hDclsQN`: `∃ W₀` after `(d m Λg K C₀ ε' D')`; conclusion is exactly the `hDcls` field of `GridAssemblyHypN`
  (`GridAssemblyN.lean:209`: `∀ ω j, j < K → j < τ ω → Cls (j+1) (δD j ω) (Dr j ω)`) with `K = Kg n`,
  `Cls = altClsQN … ε' Dc (gridTime s v Kg n)`, `δD ≡ 4W^{-D'}`, `Dr = dGridQN … (QopAlgebra_mollifier …) σ`.
  The two crude sups on `{j < Kg n, j < τ ω}` are explicit hypotheses (ticket Open issue 1, report (d) 1).
- Level-free (§62 (4)): `Γ Λ Φ` occur only inside `GoodSetN` memberships (pins above); grep of §1 = 0. No `σ`
  hypothesis; no prime pin used (§80).
Verdict on statements: all five equal their pins; the pins match the ticket's Design. No special case is passed off
as a general statement (T4's mollifier specialisation is pinned and disclosed).

## 5. Hidden hypotheses, vacuity, cycles
- No new `structure`/`class`/`def`; hypotheses are `GoodSetN` memberships, `STMollifierProps`, `EKFastDecay`,
  norms and real inequalities, all in signatures.
- Imports (file lines 6-11): `QDriftA`, `QopDecay`, `B45`, `NQGood1`, `Step2Core`, `Kernel.PropT` (merged). Instance
  helpers come from merged modules (`grep -rnE`):
```
RBM3D/Induction/GridDriftN.lean:1183:namespace GridDriftNCheck
RBM3D/Induction/AzumaProxyN.lean:924:theorem zero_mem_goodSetN_of_levels {E : ℝ} (hE : |E| < 2) {k : ℕ} (hk : 1 ≤ k)
RBM3D/Induction/AzumaProxyN.lean:970:theorem azumaProxy_pathH_zero_of_s_zero (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hs : s n = 0)
RBM3D/Loop/KLFinal.lean:243:theorem stKbound_holds (hd : 3 ≤ d) {E : ℕ → ℝ} {κ gmax : ℝ} (hκ : 0 < κ) (hg : 0 < gmax)
RBM3D/Defs/Sizes.lean:260:def sz0 : Sizes 3 where
```
  No `NQEndFlow*` or unmerged import; no circular dependency.
- No external hypothesis is introduced (no new `Prop`, registry diff empty).

## 6. Compiled nonempty instances (read in the file, lines 760-947; compiled in §3)
Each instance applies its endpoint theorem at `sz0`, `d = 3`, `m = 3` (`k = 4`), `K = 2`, `C₀ = 7`, `ε' = 1/5`,
`τ' = 1/10`, `D' = 6`, `Dc = 3`, `E = 0`, `u = 0`, `H = 0 ∈ GoodSetN` at levels `(4,100,1)` (`zero_mem_inst`,
proved), explicit mollifier (`QopAlgebra_mollifier_props`, `_differentiableAt` applied), every `σ`:
| target | instance | hypotheses left open | window non-empty |
|---|---|---|---|
| T2 | `drift13_fastDecay_instance` (`n = 9`) | none | `∃ b i j, W^{1/5}ℓ_0 ≤ zdistD` |
| T3 | `altB4N_fastDecay_instance` | none (crude sup `inst_data`/`crude_sup` from `stKbound_holds`) | same |
| T4 | `altB5N_fastDecay_moll_instance` | none | same |
| T5 | `dFlowQN_clsQN_instance` (`uu ≡ 0`, `i = 1`) | none (block sup `crude_block`; T3/T4 used for the `ℬ₄`, `ℬ₅` premises; `hDD` by `hDD_inst`) | `∃ b, ℓ_0W^{1/5} ≤ diam_∞ b` |
| T6 | `alt_hDclsQN_instance` (`s≡0, v≡1/2, Kg≡4, τ≡1`, `j = 0`, every `ω`) | none (GoodSetN and both crude sups at `j = 0` via `azumaProxy_pathH_zero_of_s_zero`, `ST_gridTime_zero`) | `∃ b, ℓ_{u_1}W^{1/5} ≤ diam_∞ b` |
`Dc = 3 > 0`, `j = 0 < Kg = 4`, `τ = 1 > 0`, `L ≥ 4`, `λ_n > 0`: no `N = 0`, empty index, collapsed window or `False`
premise. Data exactly as the ticket's "Instances to compile".

## 7. Paper-delta coverage
Proposed in the prove report (d): `T2263a` (ℬ₄ decay from the crude sup alone, commutator form; paper `(A4)` gives the
sup norm only), `T2263b` (class radius `ε'`, `δD = 4W^{-D'}`, only `ℬ₁₋₃` uses (Vb)), `T2263c` (hypotheses
`L^d ≤ W^K`, `(1−u)⁻¹ ≤ W^K`, existential `W₀`). The explicit-mollifier specialisation of T4/T6 is D556 (T2239a) and
D565 (T2249a) in `docs/paper-deltas.md:1515,1524`. Crude sups as hypotheses of T6: ticket Open issue 1 (consumer S3-18a).
Every Lean/paper difference found is covered.

## 8. Observations (no effect on verdict)
- O1. The instances take an existential `n` with `W_n ≥ W₀` (report (a): `log₁₀ W ≈ 40.7`). This is the existential
  threshold shape of the merged `stQop_sub_fastDecay`/`QopDecay_*`/`QDriftA_W0` (the same device as the merged
  `QDriftAInst`, prescribed by the ticket: "`n` large"); the data themselves (`m, K, ε', D', H, levels`) are small.
- O2. Report (b) states `7730 theorems` in the registry pre-check; here `7757` (the copied cache contains main's later
  merges). No statement effect.
- O3. Report (d) 4: the clause the ticket calls (Vb) is named `hVa`/(Va) in merged files; naming only.

## Verdict
| target | verdict |
|---|---|
| T1 private copies (`QDriftB_window_of_diamInf`, `QDriftB_W0_spec`) | PASS |
| T2 `drift13_fastDecay` | PASS |
| T3 `altB4N_fastDecay` | PASS |
| T4 `altB5N_fastDecay_moll` | PASS |
| T5 `dFlowQN_clsQN` | PASS |
| T6 `alt_hDclsQN` | PASS |
Overall: **PASS**. No dispatcher sign-off needed.
