Auditor model: claude-opus-5-5
# T2238 audit (round 1) — BA-S2a `RBM3D/BA/Step1Trivial.lean`
Date: Tue Oct  6 01:57:49 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2238-audit1`, detached at `t/T2238` = `2738b7e` (merge-base with `main`: `cc4d165`). Scratch: `scratchpad/T2238/audit/`.

## 1. Scope of the diff
```
$ git diff --stat main...HEAD
 RBM3D/BA/Step1Trivial.lean | 208 +++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean     |   3 +-
$ git diff main...HEAD -- RBM3D/Test/Axioms.lean   (structuralProps tail)
-   `RBM.Endpoints.qd2Bad] -- ...
+   `RBM.Endpoints.qd2Bad, -- ...
+   `RBM.BA.BAWinBulk] -- the window `[√(1 - c₁) g₀, g₀]` lies in the `κ`-bulk ... (BA-S2a, T2238, DECISIONS §20, T2205 portmap P.2: structural)
```
Both files are sole writable. `Axioms.lean` is allowed "only if the registry pre-check flags a name"; the ticket's fallback says `BAWinBulk` goes to `structuralProps`. A flag is expected: `BAWinBulk` is a binder head of `BAFamZ_im_m_ge`, and no theorem concludes it:
```
$ grep -rn "BAWinBulk" RBM3D --include='*.lean' | grep -v Probe/ | grep -E "theorem|lemma"   (main side)
RBM3D/BA/CouplingWindow.lean:817:theorem BAWinBulk_of_dom ... : BAWinBulk_of_dom_stmt d := by
RBM3D/BA/CouplingWindow.lean:836:theorem BAWinBulk_of_dom_holds (d : ℕ) : BAWinBulk_of_dom_stmt d := ...
```
Both theorems conclude `BAWinBulk_of_dom_stmt`, not `BAWinBulk`. The ticket's Targets 4 assumption ("`BAWinBulk` (by `BAWinBulk_of_dom`)") was therefore wrong, and its own fallback rule was correctly applied. Since `cc4d165`, `main` has changed only `owedProps` in `Axioms.lean` (`git diff cc4d165 main -- RBM3D/Test/Axioms.lean`: LWCutExp, AnpDetGhStep, STStep5III, STPfStep5, PfStep5_walkConcl lines). The `structuralProps` tail is unchanged, so the 3-line patch applies cleanly; the hub should apply it as a patch, as the prove report says.

## 2. Statements (per target)
**Verbatim move B1–B4** (probe `96e4087:RBM3D/Probe/T2205Pins.lean`; (c1) applied to B4: registry sentence, then the first `(BA-S2)`):
```
$ python3 verb.py
B1 5 lines contained: True
B2 8 lines contained: True
B3 3 lines contained: True
B4 10 lines contained: True
in order: True
```
**Check-file equality** (`eq.lean` = imports of `docs/tickets/checks/T2238-check.lean` + `import RBM3D.BA.Step1Trivial` + rest of the check file + the 8 acceptance examples: 2 `rfl` for `BAFamZ`/`BATrivialLmax`, 6 `example : T2238Check.Y_pin := @RBM.BA.Y`):
```
$ lake env lean eq.lean > eq.out; echo "eq exit $?"; grep -c error eq.out
eq exit 0
0
```
So all 8 public names agree with the dispatcher's pins: `BAFamZ`/`BATrivialLmax` by `rfl`, and the 6 theorems by type ascription against `*_pin`. Quantifier order checked against the pin text: the fixed parameters `κ ε 𝔡 𝔠 sz z c₁ z'` come before `STLmaxgL`'s `∀ k ≥ 1` and the eventual-in-`n` `PrecL`. The conclusion is at the single time `fun _ => 1 - c₁`, bounded by `Bctl^(k-1)` (`STLmaxgL`, `FlowPins.lean:363`), with the law `seqP (sz.withLam 0)`. The statement stays at the one time `1 − c₁` and does not claim every `u ≤ 1 − c₁`. The ticket's "Not targets" record this, and the docstring keeps it only as a remark.

| target | statement vs pin | verdict |
|---|---|---|
| `BAFamZ` (def) | `rfl` with check `:117-119` = probe `:1252-1254` | PASS |
| `BAflow_T0_bounds` | `= BAflow_T0_bounds_pin` | PASS |
| `BAFamZ_main` | `= BAFamZ_main_pin` | PASS |
| `BAFamZ_lam0_window` | `= BAFamZ_lam0_window_pin` | PASS |
| `BAFamZ_im_m_ge` | `= BAFamZ_im_m_ge_pin` | PASS |
| `baFM_loop_det` | `= baFM_loop_det_pin` (`0 < η ≤ Im z_u`, `k ≥ 1`, bound `η⁻ᵏ (W^{-d})^{k-1}`) | PASS |
| `BATrivialLmax` (def) | `rfl` with check `:122-127` = probe `:1779-1784` | PASS |
| `BATrivialLmax_holds` | `= BATrivialLmax_holds_pin` (`∀ d`, no `3 ≤ d`) | PASS |

## 3. Hidden hypotheses, vacuity, cycles
- `BAFamZ`, `BATrivialLmax`, `BAFlow` and `BAWinBulk` are `def ... : Prop`, not structures with proof fields. `BAFlow` = `Admissible ∧ ∀ n, BAdom ...` (`FlowPins.lean:546`), and `BAWinBulk` (`CouplingWindow.lean:799`) is a plain ∀-statement on `m(E, g')` over the window.
- `BATrivialLmax_holds` concludes the pin itself; the proof uses no premise named `*_stmt`/`*Hyp`. Its imports are `CouplingWindow`, `FlowPins`, `Step1Setup` and two Mathlib modules, all merged. The new file imports no unmerged module and nothing imports it, so there is no cycle.
- No external hypothesis. `BAWinBulk` is a premise of the pin (signed design, probe text), not an added hypothesis.
- Proof route checked against the source text:
  - `η = c₁κ ≤ Im z_{1-c₁}`, by `ztOf_im` (`GLoopFlow.lean:64`; `etaOf m t = (1-t) m.im`) and `BAFamZ_im_m_ge`;
  - `baFM_loop_det`, via merged `norm_loopM_le_sharp`;
  - `s1_Wd_le_Bctl` at `u = 1 - c₁ ∈ [0, 1)`;
  - `lam n ≤ 𝔡⁻¹` from `hflow.1.2.2.2.2 = sz.WO 𝔡` (eventual; `Sizes.lean:164`).
  - The constant is `C = (c₁κ)⁻ᵏ(𝔡⁻²+1)^{k-1}`, fixed before `n`. `StochDomAt.refl` and `.const_mul_left`, then `.of_subset` with `τ' = τ`, finish the proof.
  - No power of `N` is used and no time other than `1 − c₁` appears.

## 4. Compiled nonempty instance
`Step1Trivial.lean:200-204`:
```
example (hwin : BAWinBulk sz0 zSeq (1 / 3) (1 / 2)) :
    STLmaxgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 - 1 / 3) :=
  BATrivialLmax_holds 3 (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq
    flow_sz0 sz0_lam_pos (1 / 3) (by norm_num) (by norm_num) hwin zSeq
    (BAFamZ_main sz0 zSeq (1 / 3) (fun _ => 0))
```
- The data is `d = 3`, the merged `sz0`/`zSeq` (`N_n → ∞`), and `κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `c₁ = 1/3`.
- The deterministic premises are discharged:
  - `BAFlow`, by the merged `flow_sz0`;
  - `0 < lam`, by `sz0_lam_pos`;
  - the numeric inequalities, by `norm_num`;
  - `BAFamZ`, by `BAFamZ_main`.
- `hwin` is the only hypothesis left, exactly as Targets 3 of the ticket pins it: the `sz0` window instance is BA-S3's (T2227 Not targets, §72 (2)).
- The instance is not vacuous. The prove report's (a)(ii) `num.py` table shows window `min Im m = 0.99949, 1.00000, 1.00000 ≥ 1/2` at `n = 0,1,2`, and `BAWinBulk_of_dom_holds` (merged) gives the window for some `c₁ > 0` at `κ/2`.
- The instance is the same as the ticket's text. It compiled in the direct compile of §5 (exit 0, no errors). PASS.

## 5. Build and axioms (audit worktree)
```
$ lake build RBM3D.BA.Step1Trivial
Build completed successfully (3751 jobs).
$ lake env lean RBM3D/BA/Step1Trivial.lean 2>&1 | grep -E "error|warning" | grep -v "longLine\|exceeds"; echo "file exit $?"
file exit 0
$ lake build          (whole library at t/T2238; root does not yet import the new file)
Build completed successfully (4040 jobs).
$ lake env lean ax.lean
'RBM.BA.BAflow_T0_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAFamZ_main' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAFamZ_lam0_window' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAFamZ_im_m_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baFM_loop_det' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BATrivialLmax_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ printf 'import RBM3D\nimport RBM3D.BA.Step1Trivial\n#assert_rbm_axioms\n' > reg.lean; lake env lean reg.lean > reg.out; echo "reg exit $?"; grep -ci error reg.out
reg exit 0
0
registry: 2 borrowed + 141 owed + 89 structural + 7 refuted; ...
$ grep -nE "sorry|admit|native_decide|^axiom|^ *axiom " RBM3D/BA/Step1Trivial.lean
(no hits)
```
- Frozen signatures are untouched: no merged Lean file other than the `Axioms.lean` registry list changes.
- The private helpers `Step1Trivial_seqHflowBA_herm` and `Step1Trivial_blockMat_herm` are `private` and carry the file stem (§3 (E)). The merged private lemmas stay private.
- Imports are exactly those of Targets 5 plus the two Mathlib modules of the check file.

## 6. Paper deltas
- The Lean/paper difference is Step 1 of `lem:main_ind_BA` (`7_8:1987-1990`, "same as [RBSO1D, Section 7.1]"), stated on the route (A) family `Fam(u)` at the fixed time `1 − c₁`. `docs/paper-deltas.md:1495` (**D536**, T2205b) covers it, and the report cites it without re-proposing.
- Change (c1) touches only a docstring. No new difference, so no `T2238a` is needed. PASS.

## 7. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1. The ticket's Targets 4 expected no registry line, but `BAWinBulk` is not concluded by any theorem, so the pre-check flags it. The prover applied the ticket's own fallback (`structuralProps`) and reported it in (b) and (d). The dispatcher may reclassify it.
- O2. Prove report (b): the narrative says `0 < 𝔡` is "unused beyond its role in `BAFlow`". In fact `h𝔡` is introduced and not referenced in the proof, which is consistent with that wording. This is harmless; the pin shape is the consumers'.
- O3. `t/T2238` is based on `cc4d165`. The hub should merge `Axioms.lean` as the 3-line patch, not as a file copy, because `main` has since changed `owedProps`. See the prover's merge note.

## Verdict
All 8 targets (`BAFamZ`, `BAflow_T0_bounds`, `BAFamZ_main`, `BAFamZ_lam0_window`, `BAFamZ_im_m_ge`, `baFM_loop_det`, `BATrivialLmax`, `BATrivialLmax_holds`): **PASS**. Ticket T2238: **PASS**. No dispatcher sign-off required. O1 is the dispatcher's option.
