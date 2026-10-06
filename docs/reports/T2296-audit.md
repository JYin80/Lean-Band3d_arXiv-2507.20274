Auditor model: claude-opus-5-5

# T2296 audit (BA-G1, `RBM3D/BA/GreenSchur.lean`), round 1 — Tue Oct  6 13:27:14 UTC 2026

Branch `t/T2296` = 1bc0c0c (merge base `main` 59a0ab5); audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2296-audit1` (detached at 1bc0c0c).
Scratch: `<scratchpad>/T2296/eq.lean` (check-file equality + axioms), `<scratchpad>/T2296/reg.lean` (registry pre-check).

## 1. Diff scope (sole writable file only)
```
$ git diff --stat main...t/T2296
 RBM3D/BA/GreenSchur.lean | 615 +++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 615 insertions(+)
$ git diff --name-status main...t/T2296
A	RBM3D/BA/GreenSchur.lean
```
No merged file touched (no frozen signature changed); `RBM3D/Test/Axioms.lean` untouched (registry pre-check below flags nothing). 615 lines < 1500: preset cut not triggered.
Imports (`grep ^import`): `BA.CombesThomas, BA.ImmLower, BA.FlowPins, Green.EntryCore, Defs.RadialSum, Analysis.Resolvent` — exactly the ticket list. `ImmLower` is kept although no `BAm_im_lower*` is used: the prove report (b) shows that without it `RBM.BA.CouplingWindowInst`/`flowP_data` (instances) are unknown, i.e. it is the transitive route to `CouplingWindow`. Observation only.

## 2. Build (audit worktree)
```
$ lake build RBM3D.BA.GreenSchur 2>&1 | grep -Ev '^✔|^⣿|^info: ' | tail
warning: RBM3D/BA/GreenSchur.lean:27:100: This line exceeds the 100 character limit, please shorten it!
Build completed successfully (3742 jobs).
exit 0
```
Only longLine linter warnings (docstring lines 17–27); no errors.

## 3. Statement check: compiled check-file equality (script)
`eq.lean` = check file `docs/tickets/checks/T2296-check.lean` + `import RBM3D.BA.GreenSchur`, its `BAflowPert` def deleted and every use replaced by `RBM.BA.BAflowPert`, then:
```
example (d : ℕ) : RBM.BA.T2296Check.BAflow_real_pin d := @RBM.BA.BAflow_real d
example (d : ℕ) : RBM.BA.T2296Check.BAflow_lam0_window_pin d := @RBM.BA.BAflow_lam0_window d
example (d : ℕ) : RBM.BA.T2296Check.BAMfine_eq_pin d := @RBM.BA.BAMfine_eq d
example (d : ℕ) : RBM.BA.T2296Check.BAMfine_norm_le_one_pin d := @RBM.BA.BAMfine_norm_le_one d
example (d : ℕ) : RBM.BA.T2296Check.BAMfine_decay_pin d := @RBM.BA.BAMfine_decay d
example : RBM.BA.T2296Check.BAMB_row_l1_pin := @RBM.BA.BAMB_row_l1
example : RBM.BA.T2296Check.BAMfine_row_l1_pin := @RBM.BA.BAMfine_row_l1
example (d : ℕ) : RBM.BA.T2296Check.BAGt_sub_BAMfine_pin d := @RBM.BA.BAGt_sub_BAMfine d
example : RBM.BA.T2296Check.BAPsiI_inBlock_pin := @RBM.BA.BAPsiI_inBlock
example : RBM.BA.T2296Check.green_diag_split_pin := @RBM.BA.green_diag_split
example : RBM.BA.T2296Check.green_off_split_pin := @RBM.BA.green_off_split
-- merged BAflowPert = check-file body, by rfl
example {d} (sz : Sizes d) lam0 E n t ω : RBM.BA.BAflowPert sz lam0 E n t ω =
  (Matrix.of fun i j => Sizes.seqHflow (sz.withLam 0) n t ω i j) + ((t : ℂ) * BAmF sz lam0 E n) • 1 := rfl
$ lake env lean eq.lean 2>&1 | grep -v warning   # (the 43 `#check` echoes of section 1 omitted)
'RBM.BA.BAflow_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAflow_lam0_window' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMfine_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMfine_norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMfine_decay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMB_row_l1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMfine_row_l1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAGt_sub_BAMfine' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAPsiI_inBlock' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.green_diag_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.green_off_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenSchurInst.inst_BAFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenSchurInst.inst_green_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```
All 11 targets are definitionally the dispatcher's pins (same binders, order, hypotheses, constants), and `BAflowPert` is the check-file def verbatim.
Against the ticket's mathematics (read from the signatures): T1 `∀ n` from `BAFlow`, m = `BAmF` (not free); T2 `∀ᶠ n`, `0 < g₀ ≤ 𝔡⁻¹`; T3 needs only `0 < Im m`; T4 `BASelf` at real `E`; T5/T7 rate `BAct_rate d Λ κ` (depends on `d, Λ, κ` only), `3 ≤ L`, `0 < g ≤ Λ`, no small/large branch premise; T6/T7 `d = k + 2`, constant independent of `L, W`; T8 `t < 1`, no `0 ≤ t`, both orders; T9 all `d L W`; T10/T11 generic `ι β`, supports of `D`, `X` as explicit hypotheses (a.s. block support deferred to BA-G2 as the ticket says). No special case passed for a general target.

## 4. Hidden hypotheses / vacuity / cycles
- Hypotheses are merged data predicates (`BAFlow`, `BAReal`, `BASelf`), order relations, and the explicit support relations `hD`, `hX`; no new `def … : Prop`, no structure carrying a hypothesis.
- Dependencies (`lake env lean` resolved them from `main`'s oleans): `BAm_self`, `BAdom_real`, `BAm_real_eq_of_self`, `BAt0_pos`, `BAt0_lt_one`, `BASelf_subord`, `BASelf_unique`, `BAmSubord` (`BA/MFixedPoint.lean`), `BAMB_row_sq_real` (`BA/Ward.lean`), `BAMB_decay_large`, `BAct_rate_pos` (`BA/CombesThomas.lean`), `BAMres_fine_apply` (`BA/FlowPins.lean`), `green_diag_paper`, `green_off_diag_paper` (`Green/EntryCore.lean`), `sum_radial_exp_decay_le`, `isUnit_sub_smul_of_isHermitian`, `ztOf_im` — all merged; nothing imports `ConArg`/`Step1*`; no cycle (new leaf module).
- No external hypothesis introduced (no limit check needed).
```
$ grep -nwE 'sorry|admit|axiom|native_decide' RBM3D/BA/GreenSchur.lean ; echo $?
1
$ for n in <11 targets> BAflowPert GreenSchurInst GreenSchur_; do git grep -lw $n main -- RBM3D | wc -l; done
BAflow_real 0  BAflow_lam0_window 0  BAMfine_eq 0  BAMfine_norm_le_one 0  BAMfine_decay 0  BAMB_row_l1 0
BAMfine_row_l1 0  BAflowPert 0  BAGt_sub_BAMfine 0  BAPsiI_inBlock 0  green_diag_split 0  green_off_split 0
GreenSchurInst 0  GreenSchur_ 0
```
Unpinned helpers are `private` with prefix `GreenSchur_`; instance theorems live in `RBM.BA.GreenSchurInst` (rule (E)).

## 5. Registry pre-check
```
$ printf 'import RBM3D\nimport RBM3D.BA.GreenSchur\n#assert_rbm_axioms\n' > reg.lean; lake env lean reg.lean 2>&1 | tail -2
non-vacuity certificates: 0 of 147 premises in the two ledgers; the rest are not known to be satisfiable (...)
registry pre-check exit 0
```
No name flagged; `Test/Axioms.lean` correctly untouched.

## 6. Compiled nonempty instances (all in `GreenSchur.lean` §5, compiled by the build in §2)
| Target | Instance | Data (nondegenerate) | Open hypotheses |
|---|---|---|---|
| 1 | `inst_flow_real` (:602) | `inst_BAFlow` (:542): `d=3`, `L≡4`, `W_n=n+1`, `lam≡1/100`, `z≡w−m_w`, `w=11i/10`, `κ=9/10`, `ε=1/2`, `𝔠=1/9`, `𝔡=1/2`; `N_n=(4(n+1))³→∞` | none |
| 2 | `inst_flow_window` (:608) | same `BAFlow` witness | none |
| 3 | `inst_Mfine_eq` (:389) | `szP` (`L=4`, `W=2`), `g0P, EP`, `x=0 ≠ y=(fun _ => 1)` | none |
| 4 | `inst_Mfine_norm` (:398) | `szP`, `BASelf` from `flowP_data` | none |
| 5 | `inst_Mfine_decay` (:402) | `d=3`, `Λ=g0P`, `κ=Im mS 4 10`, `L=4` | none |
| 6 (I1) | `inst_row_l1` (:382) | `k=1`, `L=4`, `Λ=g=g0P`, `κ=Im mS 4 10`, `flowP_real`, `g0P_pos` (as ticket) | none |
| 7 | `inst_Mfine_row_l1` (:409) | `k=1`, `szP`, same data | none |
| 8 | `inst_Gt_sub_Mfine` (:416) | `szP`, `t=1/2`, `ω≡1`, `Im m>0` | none |
| 9 (I2) | `inst_PsiI_inBlock` (:427) | `d=3, L=4, W=2`, same block, `x ≠ y`, different offsets (all by `decide`) | none |
| 10, 11 (I3) | `inst_green_diag` (:456), `inst_green_off` (:480) | `ι=β=Fin 2`, `b=id`, `X=0`, `D=!![0,1;1,0]`, `z=i`; `det=−2` (`GreenSchur_D2_det`), `G₀₀≠0` (`GreenSchur_D2_G00`) | none |

The `BAFlow` witness is a genuine nonvacuity certificate for the chain-domain hypothesis of T1/T2: `Im z = 11/10 − Im m_w ∈ [0.19, 0.2]`, `9/10 ≤ Im m_w ≤ 10/11` (from `BASelf_subord`), `N^{-1/2} ≤ 1/8`, `(eq:WO)` from `n ≥ 99`, `W ≥ N^{1/9}` from `n ≥ 1`; no astronomically large witness, no `N = 0`, no collapsed window, no `False` premise.

## 7. Paper-delta coverage
| Lean/paper difference | Coverage |
|---|---|
| T5 `(Mbound_AO2)` (`7_8:1902`, stated for `λ ≥ (2C)⁻¹`, unspecified `c`) proved for every `0 < g ≤ Λ` with `c = BAct_rate d Λ κ` | existing D602 (T2290a, `docs/paper-deltas.md:1561`, working tree) |
| real-axis datum `BAReal` (`κ ≤ Im m`) instead of `(eq:WO)` + bulk window | existing D403 (cited by T2290 audit) |
| T6, T7 (`ℓ¹` rows), T9, T10/T11 split with explicit support hypotheses | not paper statements (corollaries / algebra of `(4.7)`,`(4.8)`); no delta needed; T10/T11 BA support deferred to BA-G2 per ticket |
| T8 for every real `t < 1` (paper `t ∈ [0,1)`; for `t < 0`, `√t = 0` in Lean) | weaker-hypothesis extension, mentioned in prove report (d); no statement conflict — observation |
Prove report (d): "Paper-delta candidates: none new" — consistent with the above.

## 8. Observations (no RETURN)
- O1: longLine linter warnings at lines 17–27 despite `set_option linter.style.longLine false` (set after the module docstring). Cosmetic.
- O2: `RBM3D.BA.ImmLower` import is used only transitively (for `CouplingWindowInst`), as the prove report shows; the ticket allows keeping it.

## 9. Verdict
| Target | Verdict |
|---|---|
| 1 `BAflow_real` | PASS |
| 2 `BAflow_lam0_window` | PASS |
| 3 `BAMfine_eq` | PASS |
| 4 `BAMfine_norm_le_one` | PASS |
| 5 `BAMfine_decay` | PASS |
| 6 `BAMB_row_l1` | PASS |
| 7 `BAMfine_row_l1` | PASS |
| 8 `BAGt_sub_BAMfine` (+ def `BAflowPert`) | PASS |
| 9 `BAPsiI_inBlock` | PASS |
| 10 `green_diag_split` | PASS |
| 11 `green_off_split` | PASS |

**Ticket T2296: PASS.** No dispatcher sign-off needed. The hub's full `lake build` at merge remains required.
