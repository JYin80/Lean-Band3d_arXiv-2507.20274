Auditor model: claude-opus-5-5

# T2179 audit, round 1 (S3-11, `RBM3D/Induction/NQBudget.lean`), Mon Oct  5 06:53:32 UTC 2026

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2179-audit1`, detached at `t/T2179` = c3ce744. Scratch: `scratchpad/T2179/`.

## 1. Diff scope, hygiene, build, axioms
```
$ git diff --name-only main...t/T2179
RBM3D/Induction/NQBudget.lean
$ git diff --diff-filter=M --name-only main...t/T2179 | wc -l      (modified existing files: frozen signatures)
0
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom|^\s*axiom " RBM3D/Induction/NQBudget.lean | wc -l
0
$ lake build RBM3D.Induction.NQBudget ; echo exit=$?
ℹ [3840/3840] Built RBM3D.Induction.NQBudget (13s)
Build completed successfully (3840 jobs).
exit=0
$ grep -n "NQBudget.lean" build.out | grep -v "depends on axioms"        (warnings/errors from the new file)
(no output)
$ grep "NQBudget.lean.*depends" build.out | sed 's/.*depends on axioms: //' | sort | uniq -c
  26 [propext, Classical.choice, Quot.sound]
$ grep -rnwE "NQBudgetInst|nqBudget_[A-Za-z_0-9]*|tbInitN|tbDriftN|tbQvN|tbInitNonAltN|tbDriftNonAltN|tbQvNonAltN|budgetNonAltN|qvBdNonAltN_eq_qvShape|assembledRHSNonAltN" RBM3D | wc -l   (main worktree)
0
```
The 26 `#print axioms` lines cover the 18 target names and the 8 named instance theorems. `RBM3D/Test/Axioms.lean` is unchanged, as the ticket expects (the file adds no `Prop` pin).

## 2. Target 1 (four pinned definitions) and the `budgetNonAltN` pin: script diff plus compile check
```
$ python3 scratchpad/T2179/defdiff.py
assembledRHSNonAltN identical 15
nqBudget_qvShape identical 2
nqBudget_kapFar identical 3
nqBudget_qvFar identical 4
thm hyp names: hk hε₁ hE hs0 hsv hv1 hK hη hΔη hΓ hΛ hΦ hlog hX0 hR ha1 ha2 ha3 he1 he2 he3 he4
#pin hyps 22 #thm hyps 22
names as pinned: True
  differs only in parentheses: hlog
  differs only in parentheses: hR
identical 20 paren-only 2
conclusion identical: True
thm binders: {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (Λg κ' ε : ℝ) (Γ Λ Φ : ℕ → ℝ) (D' D'' D_Y D_t τK εq ε₀ ε₁ X0 : ℝ) (a : Fin k → Zd d (sz.L n))
pin binders: {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (Λg κ' ε : ℝ) (Γ Λ Φ : ℕ → ℝ) (D' D'' D_Y D_t τK εq ε₀ ε₁ X0 : ℝ) (a : Fin k → Zd d (sz.L n))
```
The parentheses (`(∑ …) ≤ X` against `∑ … ≤ X`) parse the same way. The compile check below settles it. Scratch file `AuditPin.lean`: `import RBM3D.Induction.NQBudget`, then check-file §§2–3 verbatim in `RBM.Ind.T2179Check`, then:
```
example : @assembledRHSNonAltN = @RBM.Ind.assembledRHSNonAltN := rfl
example : @nqBudget_qvShape = @RBM.Ind.nqBudget_qvShape := rfl
example : @nqBudget_kapFar = @RBM.Ind.nqBudget_kapFar := rfl
example : @nqBudget_qvFar = @RBM.Ind.nqBudget_qvFar := rfl
theorem audit_pin_ok : budgetNonAltN_pin := @RBM.Ind.budgetNonAltN
$ lake env lean AuditPin.lean; echo exit=$?
'RBM.Ind.T2179Check.audit_pin_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```
The bare term `@RBM.Ind.budgetNonAltN` elaborates at type `budgetNonAltN_pin`, and the binders, the 22 hypotheses and the conclusion all agree. The vocabulary also has the shape of the merged `AssembledN` right-hand side (`GridAssemblyN.lean:248-256`) at `m = K n`: `κ 0 m·X0 + εK 0 m·δ0 + Δ Σ(κ(j+1,m) dDrift_j + εK(j+1,m) δD_j) + N^ε √(Σ c) + N^{-D} + Σ (1+(1-u_m)⁻¹)^k stepErr_j`.

## 3. Targets 2–5 (unpinned shapes) against the ticket's mathematics
I compared the statements extracted in prove (b) with the source, `RBM3D/Induction/NQBudget.lean:118-857`.
- `nqBudget_im_le_one`, `_inv_one_sub_le` (`|E|<2`, `v<1`, `η_v⁻¹ ≤ N` ⊢ `(1-v)⁻¹ ≤ N`), `_sum_succ_le` (`0 ≤ f 0`), `_sqrt_add_le`, `_kappa_le_kapFar` (`0 ≤ u_i ≤ u_m < 1`, `(1-u_m)⁻¹ ≤ N`; no hypothesis on `sz.lam n`): these match the ticket item by item.
- `tbInitN`, `tbDriftN`: these are the RBM2D `tbInit`/`tbDrift` hypotheses (`NonAltBudget.lean:189-197` at c9a24cf, read with `git show`) with `(scaleM^k)⁻¹ ↦ B^k`. The conclusions match the ticket. `tbQvN` adds `hB0 : ∀ j < K, 0 ≤ B (j+1)`, which is the ticket's "`0 ≤ B i`".
- `qvBdNonAltN_eq_qvShape`: the weights are `W^{Cε} r^{k-1}`, `W^C`, `W^C W^k`, `Γ(ΓΛ)`, `W^{-D''}`, `B_u`, `η_u`, as pinned in the prose.
- `tbInitNonAltN`, `tbDriftNonAltN`, `tbQvNonAltN`: the hypothesis lists are exactly the ticket's. The drift level is `a = Γ(ΓΦ)((k-1)+kΓΦ)` with `b = 0`. The far parts are `(KΔ)(W^C W^{-D'})` and `(KΔ)(k·qvFar·W^{-D''})`.
- `nqBudget_merged_inputs`: its premises are exactly those of `SumWeightedStepErrN_Stmt` (`GridEnvelopeN.lean:595-607`, with `t ↦ v`), in the same order. Its conclusion is `hlog ∧ hR` of `budgetNonAltN`, literally the same text. The proof is `filter_upwards` over the merged `sum_gridStep_div_etaT_le` and `sum_weighted_stepErrN_le`, instantiated at `m = K n`.
- §29 checklist: `0 ≤ s n ≤ v n < 1` are premises; there is no `lemT`, `g²/L²`, `Bandwidth` (docstring only), `W ≥ N^𝔠`, `1 < W`, or lower bound on `lam`; everything is deterministic at fixed `n`.

## 4. Hidden hypotheses, vacuity, cycles
- No structure-typed hypotheses. Every premise is a real or ℕ inequality, an equation, or a merged `Prop` (`SizeTendsto`, `RangeCond`).
- No circularity. The imports are `Induction/NQGood2`, `Induction/GridEnvelopeN` and `Induction/ContinuityNet`, all merged on `main`. The file uses no other ticket's unmerged pin.
- Vacuity: instance (c) below discharges all 22 hypotheses of `budgetNonAltN` at once, at nondegenerate data. `budgetNonAltN` has no external (paper-cited) hypothesis. `ha1`–`he4` are numerical. The preflight `lim.py` table in prove (a), read as corrected in (a′), shows all seven columns negative at `n = 10⁶` for `C ∈ {1/2, 1, 5, 20}`. That is the lesson-14 limit check for the consumer regime. Target 5 is checked eventually at `GridEnvelopeNCheck` data (instance (d)).

## 5. Compiled nonempty instances (namespace `RBM.Ind.NQBudgetInst`, same file; all compiled in §1)
| target | instance | data |
|---|---|---|
| `tbInitN`, `tbDriftN`, `tbQvN` | `tbInitN_instance` `:945`, `tbDriftN_instance` `:955`, `tbQvN_instance` `:974` | `K = 4`, `k = 3`, `κ ≡ 2`, `ε ≡ 1`, `B i = sz0.Bctl 0 (u i)` (positive, monotone, proved), `η > 0` proved |
| target 2 (5 facts) | `example`s `:991-1024` | `E = 1/2`, `v = 1/32`, `N = 2^21`, grid `u_j = j/128`, `i = 1`, `m = 4` |
| `qvBdNonAltN_eq_qvShape`, `tbInitNonAltN`, `tbDriftNonAltN`, `tbQvNonAltN` | `example`s `:1026-1082` | `d = 3`, `sz0`, `n = 0`, `Einst`, `sInst`, `vg`, `Kg`, `k = 3`, `Λg = 10`, `κ' = 1/2`, `ε = 4/5`, `Γ4`, `Λ3`, `Φ1`, `D' = 6`, `D'' = 5`, `aFar` |
| `budgetNonAltN` | `budgetNonAltN_instance` `:1412` | same data; `ε₁ = 2/21`, `X0 = 4B_0^3`, `τK = 1/21`, `εq = 1`, `D_Y = 1`, `D_t = -5`, `ε₀ = nqGood1C 3 3 10 (1/2) + 12` |
| `nqBudget_merged_inputs` | `nqBudget_merged_inputs_instance` `:1437`, `_exists` `:1461` | `κ = 1`, `τ' = τK = 1/2`, `C_K = 21`, `D_t = 1`, `E1`, `s ≡ 0`, `v ≡ 1/2`, `Kc` |

In `budgetNonAltN_instance` every argument is a proof term, and no hypothesis is left open:
```
(by norm_num) (by norm_num) (Einst_abs_lt 0) (by norm_num [sInst]) (by norm_num [sInst, vg]) (by norm_num [vg]) (by norm_num [Kg]) eta_inv_le_N
(by rw [step0]; linarith [eta_inv_le_v]) (by rw [N_eps1]) (by norm_num [Λ3]) (by norm_num [Φ1]) hlog_instance (by rw [N_eps1]) hR_instance
(ha1_inst _ Cpos) (ha2_inst _ Cpos) (ha3_inst _ Cpos) (he1_inst _ Cpos) (he2_inst Cpos) (he3_inst _ Cpos) (he4_inst _ Cpos)
```
`hR_instance` (`:1241`) proves the sum is at most `N^5`. It does this by bounding `envConst`, `kStepC` and `uStepC` at `n = 0`. `hlog_instance` (`:1271`) proves that the sum, which is at most `4·(1/128)(11/10)`, is at most 14, and 14 is at most `Ls`. `ha1`–`he4` are proved for every `C > 0` (with `Cpos` from `nqGood1C_pos`). The instance data are exactly the ticket's items (a)–(d). The case `N = 0`, an empty index set, a collapsed window and a `False` premise are all absent: `K = 4`, `Δ = 1/128`, `v - s = 1/32`.

## 6. Paper-delta coverage
Prove (d) proposes the following:
- `T2179a`: the target `N^{ε₀}(Λ^{1/2}+Φ+Φ²)B_v^k`, with the `Φ²` coming from (D2), against RBM2D's `(Λ^{1/2}+Φ)M_v^{-k}`.
- `T2179b`: `Δη_v⁻¹ ≤ 1` in place of `ΔN ≤ 1`.
- `T2179c`: the far parts carry `W^C`, so `D'` and `D''` are chosen after `C`.
- `T2179d`: `N⁻¹ ≤ B_v` in place of `M_v ≤ N`, and the `kapFar` bound.
- `T2179e`: the shape of `ha2`.

These cover every expected delta the ticket lists, plus the `ha2` shape. The statement does not differ from the paper anywhere else. The items in §7 are equivalent or weaker forms and are not statement differences.

## 7. Observations (no RETURN)
- `tbQvNonAltN` writes `(W^{Cε})^2` where the ticket's prose has `W^{2Cε}`. The two are equal because `W ≥ 0`. The prose was not a pin.
- In `tbInitNonAltN` the hypothesis `hs0` is kept as listed in the ticket but is not used.
- In instance (c), `ε₀ = C + 12` and `D_t = -5` are the ticket's own choices for the single size `n = 0`. The asymptotic regime is covered by the preflight limit table, not by this instance.
- `nqBudget_merged_inputs` inherits `0 ≤ D_t` from the merged statement, as prove (d) records.
- Prove (a) line 78 misreads its own table. (a′) corrects this, and no statement or verdict changes.

## 8. Verdicts
| target | verdict |
|---|---|
| 1 `assembledRHSNonAltN`, `nqBudget_qvShape`, `nqBudget_kapFar`, `nqBudget_qvFar` | PASS (verbatim, `rfl` against the check file) |
| 2 `nqBudget_im_le_one`, `_inv_one_sub_le`, `_sum_succ_le`, `_sqrt_add_le`, `_kappa_le_kapFar` | PASS |
| 3 `tbInitN`, `tbDriftN`, `tbQvN` | PASS |
| 4 `qvBdNonAltN_eq_qvShape`, `tbInitNonAltN`, `tbDriftNonAltN`, `tbQvNonAltN`, `budgetNonAltN` | PASS (`budgetNonAltN : budgetNonAltN_pin` compiles) |
| 5 `nqBudget_merged_inputs` | PASS |

Overall: **PASS**. No dispatcher sign-off is needed.
