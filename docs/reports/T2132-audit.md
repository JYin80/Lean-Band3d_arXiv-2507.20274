Auditor model: claude-opus-5-5

# T2132 audit (S3-13a, `RBM3D/Induction/QGridA.lean`) — round 1

Written Sun Oct  4 12:26:31 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2132-audit1`, detached at `t/T2132` = `b28c8be`.
The check file `docs/tickets/checks/T2132-check.lean` pins no statement text (only `#check` of merged names), so each statement is checked against the ticket's mathematics, the paper (`3_5:1300–1346`), the merged `gridDriftN_at`/`stoppedDuhamelN_at`, and RBM2D `AltGridQ.lean@c9a24cf`.

## 0. Diff scope, hygiene, build, axioms
```
$ git diff --name-only main...t/T2132
RBM3D/Induction/QGridA.lean
$ grep -nE "\bsorry\b|\badmit\b|^axiom|[^_]axiom |native_decide|set_option.*(debug|skip)" RBM3D/Induction/QGridA.lean; echo "grep exit=$?"
grep exit=1
$ lake build RBM3D.Induction.QGridA 2>&1 | tail -1 ; grep -c warning <log restricted to QGridA>
Build completed successfully (3769 jobs).
0
```
`#print axioms` lines of the build log for `QGridA.lean`, grouped by axiom set (script `sed|awk`):
```
[propext, Classical.choice, Quot.sound]: aTrueQN dGridQN aFrozQN martIncQN rGridQN lkEnvN driftEnvN qStepErrN qErrQN QGridA_Taylor2 QGridA_mollifier_taylor2 QGridA_condExp_aTrueQN QGridA_gridDriftQN_of gridDriftQN stoppedDuhamelQN QGridACheck.lam_pos QGridACheck.gridDriftQN_instance QGridACheck.stoppedDuhamelQN_instance QGridACheck.taylor2_instance
[propext, Quot.sound]: QGridACheck.sigma4_alternating
[propext]: QGridACheck.sigma4
```
Registry pre-check (scratch `import RBM3D` + `import RBM3D.Induction.QGridA` + `#assert_rbm_axioms`, after `lake build RBM3D` in the audit worktree):
```
Build completed successfully (3877 jobs).
axiom audit: 3954 theorems, 1369 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms: ...
registry exit=0
```
No frozen signature touched (only a new file). Public names outside `QGridACheck`: the nine pinned definitions, the two targets, and `QGridA_`-prefixed helpers (`QGridA_Taylor2`, `QGridA_mollifier_taylor2`, `QGridA_condExp_aTrueQN`, `QGridA_gridDriftQN_of`), as §3 (E) requires.

## Target 1 — the definitions: PASS
- `aTrueQN = STQop ϑ u_j (AvecN … j σ ω)`: `A^Q_j = 𝒬_{u_j}A_j` (`Def:QtPt`). `ϑ` is an explicit parameter of every definition, as the ticket requires.
- `dGridQN` (QGridA.lean:1274–1288) is `𝒬_u D + (𝒬_u(Θ X) − Θ(𝒬_u X)) − STPsum X (a 0) · ∂_uϑ_{u,a}`, where `D` is the merged `gridDriftN` drift (`Σ_{l=3}^{m+1} STksimLKM + STelklkM + STegtM`, letter for letter as in `gridDriftN_at`) and `Θ = ThetaN … (fun i => mSigma (E n) (σ i)) u`. The paper (`3_5:1345`, `3_5:1315`) has:
```
{\cal B}_5(u):= -\br{{\cal P} \circ\left(\mathcal{L} - \mathcal{K}\right)^{(n)}_{u, \bsig}}\cdot \partial_u  \dthn^{(n)}_{u }
- \left[{\cal P} \circ \left(\mathcal{L} - \mathcal{K}\right)^{(n)}_{t,\bsig}\right]_{a_1} \big(\partial_t \dthn_{t,\ba}^{(n)}\big) \dd t.\label{zjuii1}
```
  So the Lean last term is `+ℬ₅` with the paper's printed sign, and `ℬ₄ = [𝒬_u, ϑ^{(n)}_{u,σ}](𝓛−𝒦)` (here `ϑ^{(n)}` is the propagator `Θ`) matches `3_5:1345`. RBM2D defines `B5 = +Psum(𝓛−𝒦)(a 0)·ϑ̇` (`HierVocab.lean:268`) and subtracts it (`AltGridQ:942`: `… + B4 − B5`), so the two Lean drifts agree. The 3D paper prints `−`, so there is no #122-type sign delta here, as the report says.
- `lkEnvN`, `driftEnvN` and `qStepErrN` are RBM2D's with `W² → W^d`, `L² → L^d` and `Lp = (L^d)^m` (`m+1 = k` indices). The two changes are deliberate: the mollifier constants `C` and `C₂` are explicit, replacing RBM2D's `2(k−1)` and `2(k−1)²`. `qErrQN` plugs in the merged `stepErrN d L W E (m+1) u_j u_{j+1} Δ Bk`. Index type `Fin (m+1)`, no `[NeZero k]`.

## Target 2 — `gridDriftQN`: PASS
Hypotheses compared by script with the merged `gridDriftN_at` (`GridDriftN.lean:777`):
```
$ diff <hyps of gridDriftN_at> <hyps of gridDriftQN>
7,8c7,9
< (hk : 2 ≤ k)
< (σ : Fin k → Bool)
---
> (hlam : 0 < sz.lam n)
> (hm : 1 ≤ m)
> (σ : Fin (m + 1) → Bool)
$ diff <hB of gridDriftN_at> <hB of gridDriftQN>
2c2
<       J.WF → 2 ≤ J.length → J.length ≤ k →
---
>       J.WF → 2 ≤ J.length → J.length ≤ m + 1 →
```
- The conclusion is the ticket's: `∀ᵐ ω, ∀ a, ‖𝔼[A^Q_{j+1}|F_j] − 𝒰_{u_j,u_{j+1}}A^Q_j − Δ·dGridQN_j‖ ≤ qErrQN_j`. The quantifier order is the same as RBM2D `gridDriftQN` (`AltGridQ:1536`), with the hypotheses at index `n` only (`_at` form, DECISIONS §29 (4)).
- `hlam : 0 < sz.lam n` is a genuine hypothesis. `Sizes.lam` has no positivity field; positivity holds only eventually, by `eq:WO`. The report lists it under T2132d.
- Time regularity uses route (b) of the ticket. `gridDriftQN` is stated for the merged `QopAlgebra_mollifier d L m (sz.lam n)`, and its proof (QGridA.lean:2129–2133) discharges every mollifier input with merged or proved lemmas: `QopAlgebra_mollifier_props`, `QopAlgebra_mollifier_differentiableAt` and `QGridA_mollifier_taylor2`. No hypothesis is hidden in a structure.
- The general engine `QGridA_gridDriftQN_of` carries the second-order bound `QGridA_Taylor2 C₂ ϑ` and `hdiff` (`DifferentiableAt` on `[0,1)`) as explicit hypotheses.
- `QGridA_Taylor2` (QGridA.lean:1224) is a plain `Prop`: `∀ u Δ, 0 ≤ u → 0 ≤ Δ → u+Δ < 1 → ∀ a, ‖ϑ(u+Δ)a − ϑ u a − Δ ∂ϑ‖ ≤ C₂(1−(u+Δ))⁻²Δ²`. It is proved for the merged mollifier, so it is not an external input and needs no limit check.
- Dependencies are merged results only (`gridDriftN_at`, `QopAlgebra_*`, `GridDuhamelN_*`). There is no cycle: QGridA imports only `Induction/{GridDuhamelN,GridDriftN,QopAlgebra,HierAlgebra,Step34Pins}`.
- The route (a) rejection is mathematics. The first-order per-step bound `Lp·Mk·2CβΔ` sums to a `K`-independent quantity. This is consistent with the ticket's item (c) not being needed, and `STMollifierProps` is unchanged.

## Target 3 — `stoppedDuhamelQN`: PASS
- The hypotheses are those of the merged `stoppedDuhamelN_at` (`hE hs0 hst ht1 hK`), plus `ϑ` (arbitrary) and `hj : j ≤ K n`.
- The merged lemma assumes `min j (τ ω) ≤ K n`; `j ≤ K n` is needed here because the frozen process propagates up to `u_j`. RBM2D's `stoppedDuhamelQN` (`AltGridQ:1627`) uses the same `m ≤ K n`.
- The conclusion `aFrozQN_j = 𝒰_{u_0,u_j}A^Q_0 + Σ_{i<j∧τ} 𝒰_{u_{i+1},u_j}(Δ dGridQN_i + martIncQN_i + rGridQN_i)` matches RBM2D's, letter for letter.
- `rGridQN` is defined by subtraction, so the identity is algebraic. The content of the remainder is bounded only by target 2, as in RBM2D/RBM1D; this is the design of the ticket, not a vacuity.

## Compiled nonempty instances (QGridA.lean:2230–2291; compiled in the build above)
- **`gridDriftQN_instance`** uses the merged `sz0` (`d = 3`, `L_0 = 4`, `W_0 = 32`, `lam_0 = 1/64`) and the `GridDriftNCheck` data `E0 ≡ 0`, `s0 ≡ 1/10`, `t0 ≡ 1/2`, `K0 ≡ 4` (`data : gridStep = 1/10, u_0 = 1/10, u_1 = 1/5`), with `n = j = 0`, `m = 3` (4 indices) and `σ = ![true,false,true,false]`. `STAlternating σ` is proved by `decide`, and the mollifier is the merged `QopAlgebra_mollifier 3 4 3 (1/64)`.
  - Every hypothesis is discharged at the data by `norm_num`, `lam_pos` and `GridDriftN_exists_envelope` (which gives `Bk` and `hB`).
  - The result is `STAlternating σ ∧ ∃ Bk ≥ 0, <the bound>`. The existential `Bk` is the merged envelope lemma's (paper-delta D234), as in `GridDriftNCheck`. Nothing is left open.
- **`stoppedDuhamelQN_instance`** uses the same data with `τ ≡ 3` and `j = 4 = K0`. So `min j τ = 3`, which gives three genuine Duhamel steps, for every `ω`. All hypotheses are discharged by `norm_num`.
- **`taylor2_instance`** applies `QGridA_mollifier_taylor2` at `d = 3`, `L = 4`, `m = 3`, `g = 1/64`.
- None of the instances is degenerate: no `N = 0`, no empty index set, no collapsed window (`s < t`, `K = 4`), no `False` premise.

## Paper-delta coverage
| Lean/paper difference | covered by |
|---|---|
| drift `𝒬_uD + ℬ₄ + ℬ₅` vs the paper's `𝒬_u Σ_k ℬ_k` (`int_K-L+Q`) | T2132a |
| second-order Taylor bound of `ϑ` (not in `STMollifierProps`/`eq:derv_Theta`) | T2132b |
| `Fin (m+1)` tensors, `m ≥ 1` vs `n ≥ 2`; no `NeZero` | T2132c |
| `_at` form, `0 < sz.lam n`, `DifferentiableAt` vs `DifferentiableOn (Ico 0 1)` | T2132d |
| `B_k` envelope `hB` as hypothesis; `stepErrN`, `GridDriftN_exists_envelope` | merged D234, D235 |
| time-discrete one-step identity / discrete Duhamel telescope (vs continuous `int_K-L+Q`) | generic D162, D163 (see O1) |

## Observations (no statement, instance, build or axiom effect)
- **O1.** D162 and D163 name `(int_K-L_ST)` and `(int_K-LcalE)`. `stoppedDuhamelQN`/`gridDriftQN` are the grid form of their counterpart `(int_K-L+Q)` (`3_5:1337`). When numbering T2132a, the dispatcher may extend its text, or that of D162/D163, to cover `int_K-L+Q` explicitly. The class of difference is already recorded.
- **O2.** The ticket's text names "the merged commutators" for the one-step algebra. Lean instead defines `ℬ₄` directly as the commutator, so `QopAlgebra_commutator_ThetaN`/`_UN` are not used. The report says so (b.8). The sum-zero bridge to the paper's `𝒬_uℬ_k = ℬ_k` is not proved here. T2132a states this, so it is open for a consumer.
- **O3.** `qStepErrN` contains `(1 + C·Lp)` with `C = (1+40dm)6^{dm}`, a constant that depends only on `(d, m)`, and `Lp = (L^d)^m ≤ N^m`. Whether the sum reaches `N^{-D_t}` is S3-13b's job. The report's section (d) gives the expected shape but marks it "not re-verified".
- **O4.** `Test/Axioms.lean` is unchanged; it needs no lines because the target file adds no owed premise. The registry pre-check above exits 0.

## Verdict
- Target 1 (definitions): **PASS**
- Target 2 (`gridDriftQN`): **PASS**
- Target 3 (`stoppedDuhamelQN`): **PASS**

Overall: **PASS**. Dispatcher sign-off is not needed.
