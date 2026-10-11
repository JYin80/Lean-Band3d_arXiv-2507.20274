Auditor model: claude-opus-5-5

# T2406 audit (round 1) — BA-E3 `baEKSumDecayNonzero_holds`

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2406-audit1`, detached at `t/T2406` = `6dfc2c9`. Time: `Sun Oct 11 03:53:49 UTC 2026` (`date -u`).

**Verdict: PASS** (target 1 PASS; C1 PASS; instances PASS; registry PASS). No dispatcher sign-off needed.

## 1. Diff scope (sole writable files only)
```
$ git diff --name-only main...t/T2406 | <match against the three sole writable files>
ok   RBM3D.lean
ok   RBM3D/BA/EKNonzero.lean
ok   RBM3D/Test/Axioms.lean
$ git diff --stat main...t/T2406 -- RBM3D/BA/EKPins.lean RBM3D/BA/FlowPins.lean RBM3D/BA/Prop6Path.lean | wc -l
       0
$ git diff main...t/T2406 -- RBM3D.lean   # one line, after the last import, before #assert_rbm_axioms
+import RBM3D.BA.EKNonzero
```
Frozen pin `BAEKSumDecayNonzero` (`BA/EKPins.lean:134`) is untouched. File length 357 lines against stop line 800.

## 2. Statement (target 1)
```
$ grep -n -A1 '^theorem baEKSumDecayNonzero_holds' RBM3D/BA/EKNonzero.lean
261:theorem baEKSumDecayNonzero_holds (d n : ℕ) (Λ κ : ℝ) : BAEKSumDecayNonzero d n Λ κ := by
$ lake env lean T2406/ax.lean   # contains: example (d n : ℕ) (Λ κ : ℝ) : BAEKSumDecayNonzero d n Λ κ := baEKSumDecayNonzero_holds d n Λ κ
exit 0
```
The conclusion is the pin by name, for all `d n Λ κ`, with no added hypotheses. The pin (`EKPins.lean:132-140`, merged T2388) reads
`3 ≤ d → 2 ≤ n → 0 < Λ → 0 < κ → ∃ C > 0, ∀ L ≥ 3, ∀ g ∈ (0, Λ], ∀ s t, 0 ≤ s → 1 - g²/L² ≤ s → s ≤ t → t < 1 → ∀ E m, BAReal d L g κ E m → ∀ σ A, (∀ i, σ i ≠ σ (finRotate n i) → i ∈ A) → ∀ 𝒜, ‖zeroModeSet d L A (BAUN … σ s t 𝒜)‖ ≤ C‖𝒜‖`.
Against the paper (`3_5_Loop_Hierarchy.tex:1666-1672`: `1-λ²/L² ≤ s ≤ t < 1`, any `σ`, `n ≥ 2`, `A ⊃ I_diff(σ)`, `‖Q^{(A)}∘𝒰∘𝒜‖_∞ ≺ ‖𝒜‖_∞`), the window, `I_diff` (cyclic, `finRotate`), the range of `A` and the norm all match. The Lean form is loss-free (`C`, not `≺`) and `C` is fixed before `L g s t E m σ A 𝒜` (proof lines 264-270: `Cs`, `C₀` obtained, `refine ⟨Ci ^ n, …⟩`, then `intro L …`). Stronger than the paper, not weaker.

## 3. Hidden hypotheses, vacuity, cycles, C1
- No structure-field hypotheses: the only data predicate used is `BAReal d L g κ E m := BASelf d L g E m ∧ κ ≤ m.im` (`BA/MFixedPoint.lean:432`), which is a pin hypothesis.
- Upstream inputs are merged theorems (on `main`): `baEKSameRow_holds : BAEKSameRow d Λ κ` (`EKPins.lean:568`), `baProp8_holds : BAProp8 d Λ κ` (`Prop6Path.lean:1009`; `BAProp8` at `FlowPins.lean:217` bounds `‖BATheta0 … 0 a‖ ≤ C (g²+|1-t|)⁻¹ ((|a|+1)^{d-2})⁻¹` for all `σ₁ σ₂`, `BAReal`, `0 ≤ t < 1`), `BAuKer_eq_one_add`, `BAMss_norm_eq_BAK`, `BAK_row_sum`, `baP8_BATheta_shift`, `BAMB_shift`, `sum_radial_pow_le`, `zeroModeSet_tensorKer`, `norm_tensorKer_le`, `norm_projMat_le`, `norm_le_sum_row_zero`. No external hypothesis, so no limit check is required.
- No cycle: imports are `BA.EKPins`, `BA.Prop6Path`, `Kernel.Evolution`, `Defs.RadialSum`; only `RBM3D.lean` imports the new module (`git grep -ln 'import RBM3D.BA.EKNonzero' t/T2406` → `RBM3D.lean`).
- C1 (no `‖m‖ = 1`, scalar `μ`, `M = m I`, smallness):
```
$ git grep -n 'PropSpin\|‖m‖ = 1\|Prop8ZeroMode\|SB d L\|mS\b\|smallness' t/T2406 -- RBM3D/BA/EKNonzero.lean
t/T2406:RBM3D/BA/EKNonzero.lean:20:`norm_zeroModeSet_UN_le`, `Kernel/Evolution.lean:629`);
t/T2406:RBM3D/BA/EKNonzero.lean:21:a scalar `μ`, `M = m I` or the smallness of `g`:
```
  (docstring lines only). The two new generic matrix lemmas (`EKNonzero_projMat_comm`, `EKNonzero_projMat_mul_Theta`) need only translation invariance; the `i ∈ A` bound (`EKNonzero_norm_projMat_mul_uKer_le`) holds for every `(σ₁, σ₂)`, so `A` may contain same-sign indices. `(1-s)L² ≤ g²` is derived from the window (`EKNonzero_coef`).

## 4. Compiled nonempty instances
```
$ grep -n '^theorem inst_\|^def AI3' RBM3D/BA/EKNonzero.lean
331:def AI3 : (Fin 3 → Zd 3 (sz0.L 0)) → ℂ := fun a => if a = 0 then 1 else 0
336:theorem inst_baEKSumDecayNonzero_n2 : ∃ C : ℝ, 0 < C ∧ AI 0 = 1 ∧
346:theorem inst_baEKSumDecayNonzero_n3 : ∃ C : ℝ, 0 < C ∧ AI3 0 = 1 ∧ (0 : Fin 3) ∉ ({1, 2} : Finset (Fin 3)) ∧
$ grep -n 'theorem hrI\|theorem LI_real\|theorem gI_le' RBM3D/BA/EKPins.lean
656:theorem gI_le : gI ≤ 1 / 64 := by
665:theorem LI_real : ((sz0.L 0 : ℕ) : ℝ) = 4 := by rw [sz0_values.1]; norm_num
668:theorem hrI : BAReal 3 (sz0.L 0) gI (1 / 2) EI mI := BAflow_real (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq flow_sz0 0
```
Both instances apply `baEKSumDecayNonzero_holds` directly (no pin as hypothesis) at `d = 3`, `L = 4`, `Λ = 1`, `κ = 1/2`, `g = gI ∈ (0, 1/64]` (`gI_pos`, `gI_le`), `BAReal` by `hrI`, `s = 1 - g²/L² < t = 1 - g²/(2L²) < 1` (`window_s`, `window_st`, `window_t`, all proved), `𝒜 = δ₀ ≠ 0`:
- `n = 2`, `σ = (+,-)`, `A = {0,1} = I_diff(σ)`; `hA` by `fin_cases`;
- `n = 3`, `σ = (+,+,-)`, `I_diff = {1,2} = A`, `0 ∉ A` stated in the conclusion, so the same-row branch is exercised; `hA` by `decide`.
Every deterministic hypothesis is discharged; nothing degenerate (`L = 4`, `n ≥ 2`, nonempty `A`, window with `s < t`, `g > 0`, nonzero tensor). Both compile (build in §5).

## 5. Build and axioms (audit worktree)
```
$ lake build RBM3D.BA.EKNonzero 2>&1 | tail -1; grep -c error build.log
Build completed successfully (3758 jobs).
0
$ lake build   # full library, registry scan included
info: RBM3D.lean:445:0: axiom audit: 11344 theorems, 3414 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4213 jobs).
exit 0
$ lake env lean T2406/ax.lean | sed 's/ depends on axioms//'
'RBM.BA.baEKSumDecayNonzero_holds': [propext, Classical.choice, Quot.sound]
'RBM.BA.EKNonzeroInst.inst_baEKSumDecayNonzero_n2': [propext, Classical.choice, Quot.sound]
'RBM.BA.EKNonzeroInst.inst_baEKSumDecayNonzero_n3': [propext, Classical.choice, Quot.sound]
$ lake env lean docs/tickets/checks/T2406-check.lean >/dev/null 2>&1; echo $?
0
$ grep -nE 'sorry|admit|native_decide|^\s*axiom' RBM3D/BA/EKNonzero.lean; echo $?
1
```
(The warnings in `build.log` are pre-existing long-line linter warnings in other modules; none in `BA/EKNonzero.lean`.)

## 6. Registry (target 4)
```
$ git diff main...t/T2406 -- RBM3D/Test/Axioms.lean | grep '^[-+] ' | sed -E 's/^([-+]) +`([A-Za-z.]+),.*/\1 \2/'
- RBM.BA.STLmaxgL
- RBM.BA.STKboundgL
- RBM.BA.STLKgL
+ RBM.BA.STLmaxgL
+ RBM.BA.STKboundgL
+ RBM.BA.STLKgL
- RBM.BA.BAEKSumDecayNonzero
```
(a) the `owedProps` line `BAEKSumDecayNonzero` is removed; (b) the three entries keep their names and positions, only the comments change. New comments (from the diff): `STLmaxgL` "owner BA-V (main induction); at BA it follows from `STLKgL` by `BALmaxFromLK_holds` once `STKboundgL` is supplied (K12)"; `STKboundgL` "owner: BA: proved at `baFMz` by `baKbound_holds` (K12); generic premise of `stBaseG_of_init`, `BALmaxFromLK`, `BAStep1`, `BABootstrap'`; discharged at BA by BA-V (instances: G7)"; `STLKgL` "owner BA-V (main induction)". "BA-K4" no longer appears in these three. This matches the ticket text. Full build with `#assert_rbm_axioms` passes (§5).

## 7. Paper deltas
The theorem proves the merged pin verbatim and adds no Lean/paper statement difference. The pin's differences (loss-free `C` in place of `≺`, `C` depending on `(d, n, Λ, κ)` only, the extra `0 ≤ s`, `BAReal` in place of `‖m‖ = 1`, `g ≤ Λ`) are those of its band twin, which D37/D38 cover, and of the BA pins of T2388 (T2388a, audited in `T2388-audit.md` §6). No new candidate is needed.

## 8. Observations (no effect on verdict)
- O1. The public instance helpers `window_s`, `window_st`, `window_t`, `AI3`, `AI3_zero` sit in namespace `RBM.BA.EKNonzeroInst`, which carries the file stem. The full build reports no name clash.
- O2. `EKNonzero_Mss_shift` and `EKNonzero_norm_Q_le` re-derive private lemmas of `Prop6Path`/`EKPins` (the prove report §(d) already names this as a cleanup candidate).
- O3. `2 ≤ n` is not used (`_hn`), as in the band proof; the statement is the pin's.

## Per-target verdicts
| target | verdict |
|---|---|
| 1 `baEKSumDecayNonzero_holds : BAEKSumDecayNonzero d n Λ κ` | PASS |
| 2 C1 (uniform BA facts only, `C = C(d,n,Λ,κ)`) | PASS |
| 3 instances `inst_baEKSumDecayNonzero_n2`, `_n3` (direct, nondegenerate, proper `A`) | PASS |
| 4 registry (deletion + three comment relabels) | PASS |
