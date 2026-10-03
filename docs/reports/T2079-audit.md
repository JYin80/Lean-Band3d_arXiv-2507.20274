Auditor model: claude-opus-5-5

# T2079 audit (S1-35, `RBM3D/Induction/Step1Setup.lean`), round 1 — Sat Oct  3 22:52:38 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2079-audit1`, detached at `t/T2079` = `be32ccb` (merge-base with `main`: `e84e0f7`; current `main` `a91ac93`).

## 1. Scope, build, axioms, hygiene

```
$ git diff --stat main...t/T2079
 RBM3D/Induction/Step1Setup.lean | 1554 +++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean          |    1 +
 2 files changed, 1555 insertions(+)
$ git diff main...t/T2079 -- RBM3D/Test/Axioms.lean | grep -c "^-[^-]"      # removed lines in the registry
0
$ lake build RBM3D.Induction.Step1Setup 2>&1 | grep -E "error|warning: declaration uses|Build completed|sorry"
Build completed successfully (3330 jobs).
$ lake build 2>&1 | grep -E "error:|Build completed"
Build completed successfully (3819 jobs).
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom " RBM3D/Induction/Step1Setup.lean; echo "grep exit $?"
grep exit 1
```
Registry pre-check plus `#print axioms` of every public declaration (67, listed by script from the file):
`import RBM3D`, `import RBM3D.Induction.Step1Setup`, 67 `#print axioms`, `#assert_rbm_axioms`, run with `lake env lean`:
```
65 of 67 lines: depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.s1_one_le_L' depends on axioms: [propext, Quot.sound]
'RBM.Ind.s1_one_le_W' does not depend on any axioms
axiom audit: 2618 theorems, 1080 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.Ind.Step1TargetV3: 1 [no certificate]          (listed under "premises THIS FORMALIZATION owes")
premises found by scanning: 83 (borrowed 2, owed 67, structural 14).
exit 0
```
(Before the full build the same file exited 1 with `1 premise(s) that no theorem ... proves [RBM.Ind.Step1TargetV3]`: the stale `Test/Axioms` olean copied from `main`. After `lake build` it exits 0.)

Name clashes against current `main` (`a91ac93`, which has 4 more modules than the merge-base):
```
$ for n in <67 short names>; git grep -n -w -F -e $n main -- RBM3D | grep -v Step1Setup
public short names with a word match in main:RBM3D (current main a91ac93): 0
```

## 2. Statements

**Key statement `Step1TargetV3`** (`Step1Setup.lean:149`) against the ticket ("its `d`-dimensional form; which conjuncts of `STStep1` it covers"):
```
def Step1TargetV3 (d : ℕ) : Prop := STGbEXPii d → STGbEXPij d → STStep1 d          -- RBM3D
def Step1TargetV3 (κ c τ : ℝ) (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=                 -- RBM2D c9a24cf:84
  KboundConcl κ → Green.GbEXPHypV3 d (κ / 2) c τ → MainIndHyp d κ c τ E s t →
    Step1LoopUnif d E s t ∧ Step1WeakLawUnif d E s t
```
Merged `STStep1` (`Induction/Defs.lean:349`): `∀ κ ε 𝔡 >0, ∀ 𝔠d ∈ (0,1/100], ∀ 𝔠 sz z, STFlow → ∀ s t, 0 ≤ s, s ≤ lemT z, s < t, t ≤ lemT z → STKbound → STLK s → STLocalMax s → STConStInd 𝔠d s t → STStep1Loop ∧ STStep1Weak`.
So `Step1TargetV3 d` concludes both conjuncts (`(lRB1)`, `(Gtmwc)`) for every datum; the RBM2D hypotheses `KboundConcl`, `MainIndHyp` (incl. `InitLK`, `InitLocal`, `CondStInd`) map to `STStep1`'s own `STKbound`, `STFlow`, `STLK`, `STLocalMax`, `STConStInd`; the only addition is the two `lem_GbEXP` parts, as universal pins (all `κ ε 𝔡 𝔠 sz z t ε₀` with `0 ≤ t ≤ lemT z`), which cover RBM2D's per-sequence `GbEXPHypV3 (κ/2)` at every time `u ∈ [s,t] ⊂ [0, lemT z]`. Quantifier order is `STStep1`'s (constants before sizes, `∀ n` hypotheses, `Prec` conclusions). It is a `def` (owed to S1-36, registered as owed); `stStep1_of_target` is the one-line application. Difference recorded as **T2079a**. PASS.

**Ported statements** (conclusion after renaming; script `concl.py`, depth-aware extraction up to `:=`):
```
s1_size_eq      RBM2D | ((d.size n : ℕ) : ℝ) = ((d.W n : ℝ) * (d.L n : ℝ)) ^ 2
                RBM3D | ((sz.size n : ℕ) : ℝ) = (((sz.W n : ℕ) : ℝ) * ((sz.L n : ℕ) : ℝ)) ^ d
s1_W_sq_le_size RBM2D | (d.W n : ℝ) ^ 2 ≤ ((d.size n : ℕ) : ℝ)
 -> s1_W_pow_le_size  | ((sz.W n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ)
s1_ratio_ev     RBM2D | (ellT u / ellT s) ^ 2 * (scaleM .. u)⁻¹ ≤ scaleM .. (s n) ^ (-((14 : ℝ)/15))
                RBM3D | sz.Bctl n (s n) * ((1 - s n) / (1 - u)) ≤ sz.Bctl n (s n) ^ ((14 : ℝ) / 15)
s1_F4           RBM2D | 6 * (s1Ms d E s n)⁻¹ ^ ((7 : ℝ) / 15) ≤ N ^ (-ε) * ((s1Ms ..)⁻¹ ^ ((1 : ℝ) / 4) / 2)
                RBM3D | (2 * (3 : ℝ) ^ d) * (s1B sz s n) ^ ((7 : ℝ) / 15) ≤ N ^ (-ε) * ((s1B sz s n) ^ ((1 : ℝ) / 4) / 2)
s1_F5           RBM2D | 2 * (s1Ms d E s n)⁻¹ ^ ((1 : ℝ) / 4) ≤ (d.W n : ℝ) ^ (-c')
                RBM3D | 2 * (s1B sz s n) ^ ((1 : ℝ) / 4) ≤ ((sz.W n : ℕ) : ℝ) ^ (-c')
s1_F6           RBM2D | ((d.size n : ℕ) : ℝ)⁻¹ ≤ (s1Ms d E s n)⁻¹ ^ ((1 : ℝ) / 4) / 2
                RBM3D | ((sz.size n : ℕ) : ℝ)⁻¹ ≤ (s1B sz s n) ^ ((1 : ℝ) / 4) / 2
s1_F8           RBM2D | ((d.W n : ℝ) ^ 2)⁻¹ ≤ s1Ms d E s n ^ (-((14 : ℝ) / 15))
                RBM3D | (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (s1B sz s n) ^ ((14 : ℝ) / 15)
s1_loop_det     RBM2D | loopAbs L W E u M σ a ≤ (2 / c₁) ^ k * (scaleM L W E u)⁻¹ ^ (k - 1)
                RBM3D | ‖loopFine d L W M (zt E u) σ a‖ ≤ (2 / c₁) ^ k * (((W : ℝ) ^ d)⁻¹) ^ (k - 1)
s1_near_card    RBM2D | ((Finset.univ.filter (fun a' : Z2 L => zdist2 L (a' - a) ≤ 1)).card : ℝ) ≤ 5
                RBM3D | ((Finset.univ.filter (fun a' : Zd d L => zdistInf d L (a' - a) ≤ 1)).card : ℝ) ≤ 3 ^ d
s1_gexRHS_le    RBM2D | gexRHS L W E u M a b ≤ 25 * B + ((W : ℝ) ^ 2)⁻¹
                RBM3D | sz.STgexRHS n E u ω a b ≤ 2 * 9 ^ d * B + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹
s1_wl_det       RBM2D | ∀ i j, llErrMat L W E u M i j ^ 2 ≤ 26 * Nτ ^ 2 * g
                RBM3D | ∀ i j, ‖sz.STGM n E u ω i j‖ ^ 2 ≤ (2 * 9 ^ d + 1) * Nτ ^ 2 * g
```
Checks:
- `M_s⁻¹ ↦ a_s = sz.Bctl n s`, `(ℓ_u/ℓ_s)² ↦ (1-s)/(1-u)`: `s1_LI`'s bound `((1-s n)/(1-u n))^(k-1) * Bctl n (s n)^(k-1)` is literally the RHS of the merged pin `STStep1Loop` (`Defs.lean:234`); `S1H55`/`s1_LI` use `STomegaC .. 2` for RBM2D's `1(gMax ≤ 2)`. `s1_ratio_ev` keeps `14/15`, needs `𝔠d ≤ 1/15` (field `h𝔠d' : 𝔠d ≤ 1/100`).
- `s1_near_card`/`s1_gexRHS_le`: merged `STgexRHS` (`Defs.lean:92`) sums two σ over `zdistInf (a'-a) ≤ 1`, `zdistInf (b'-b) ≤ 1` (ST1-COMMON item 3: `zdistInf` for stochastic statements), so `#pairs ≤ 9^d`, constant `2·9^d`; `3^d` is exact (compiled `decide`: card `= 27` at `d=3, L=4`, line 1336). The ticket's `2d+1` would be false for this ball (27 > 7); see Observation 1.
- `s1_wl_det` premises `hii`, `hij` have exactly the integrands of the merged `STGiiGEX`, `STGijGEX` (`Defs.lean:202,210`) times `Nτ`; `S1Std` (`:237`) is the RBM2D field list plus `h𝔡`, `hWO`, `h𝔠d`, `h𝔠d'` and is produced from `STStep1`'s hypotheses by `s1_std_of_stFlow` (`:259`, needs only `STFlow`, `0 ≤ s ≤ t ≤ lemT z`, `STConStInd`) — no hidden hypothesis.
- DECISIONS §26: `StochDomAt.of_subset_whp`/`of_subset_compl` (`:105`, `:125`) — signatures as in the prove report (b); absent from `Defs/StochDomAt.lean` (re-checked: `grep -n "of_subset" RBM3D/Defs/StochDomAt.lean` lists only `of_subset`, `of_subset_union`).
- DECISIONS §29: `s1_ratio_pt` has `s ≤ u ≤ t < 1` only (no `0 ≤ s`; more general); `s1_Wd_le_Bctl` keeps `0 ≤ u` and the compiled counterexample at `u = -10^6` (line 1527) shows it cannot be dropped; scale facts are `∀ᶠ n`, pin hypotheses `∀ n`; constants `2·3^d`, `2·9^d(+1)`, `(2/c₁)^k` depend on `d, κ, k` only.
- Cut and S1-36 needs (script: RBM2D names of `Step1:1-965` occurring in `Step1:967-1515`):
```
60 declarations; used by S1-36: s1_bulk s1_F3..s1_F8 s1_gMax_le s1_h55 s1_highProb_of_pt s1_hsize s1_inv_rpow s1_LI
  s1_Ms_pos s1_Mu_pos s1_one_le_L s1_one_le_size s1_pt_of_highProb s1_ratio_ev s1_std_of_mainIndHyp s1_stochDom_unit
  s1_wl_det S1H55 s1Ms S1Std s1xM s1xM_ge s1xM_le s1xM_le_add Step1TargetV3
--- used by S1-36 but absent as public name in Step1Setup: s1_Ms_pos s1_Mu_pos s1_std_of_mainIndHyp s1Ms
```
  The four are renamed `s1_B_pos`, `s1_Bu_pos`, `s1_std_of_stFlow`, `s1B` (public). Dropped RBM2D helpers (`s1_scaleM_le_W2`, `s1_ellT_nonneg`, `s1_im_le_one`, `s1_green_blockMat`…`s1_norm_loopPM`, `s1_mem_sbSupport`) are not used by S1-36.

## 3. Compiled nonempty instances (section 7, `:1135–1554`)

Data: merged `sz0`, `z0`, `flow_z0`, `sz0_admissible`; `d = 3`, `n = 0`: `L = 4`, `W = 32`, `N = 2097152`; `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `𝔠d = 1/100`; windows `[0,1/16]`, `[1/16,3/4]`, `[1/2,3/4]` (all with `s < t < 1`).
```
$ grep -c "^example" Step1Setup.lean
60
public declarations of sections 0-6: 60; each occurs in section-7 code (s1T1 :1278, s1xM :1347, rest by script)
```
- `S1Std` is discharged completely (`s1Std_sz0` `:1142`, `s1Std_sz0_const` `:1250` with `STConStInd` proved for constant windows): every deterministic hypothesis of the scale/F3–F8/ratio lemmas is discharged.
- `Step1TargetV3` instance (`:1543`): applies `stStep1_of_target` at the data above with `STFlow`, `0 ≤ s`, `s ≤ lemT`, `s < t`, `t ≤ lemT`, `STConStInd` discharged; `STKbound`, `STLK`, `STLocalMax`, `STGbEXPii/ij` and `Step1TargetV3` itself remain (other gates' pins / S1-36) — allowed.
- `s1_h55`, `s1_LI` instances on all three branches (`u<1/2`; `s<1/2≤u` via `conArg`; `s≥1/2`), with `STLK`, `STKbound` as pin hypotheses.
- `s1_wl_det`: at `u = 0` with **every** premise proved (`G_0 = mI`, `:1405`), and at `u = 1/16` with the sample event and the `STGiiGEX/STGijGEX` integrands at `ω` as hypotheses (`:1441`). `s1_gexRHS_le` at `n=0, u=1/16` with `B = η⁻²` proved (`:1383`). `of_subset_whp`, `of_subset_compl` at the merged `StochDomAtInst` data.
No `N = 0`, empty index, collapsed window or `False` premise; no astronomically large witness (all at `n = 0` or `∀ᶠ` from the merged `sz0` facts). PASS.

## 4. Paper deltas

Step 1 is not written out in the paper (`3_5_Loop_Hierarchy.tex:65`: "the same as that in [YY_25, Section 5.1] … we omit the details"); the paper-facing statements are the merged pins `(lRB1)`, `(Gtmwc)`. Lean/paper and Lean/RBM2D differences are proposed: T2079a (`Step1TargetV3` form, universal GbEXP pins), T2079b (constants `3^d`, `2·9^d`, `2·9^d+1`, `2·3^d`), T2079c (`S1Std` fields, `30 ↦ 𝔠_d`, `𝔠_d ≤ 1/15`), T2079d (`u < 1/2` regime, `W^{-d}` bound, needs `0 ≤ s` and `(eq:WO)`), T2079e (`c' = c₀/8`). Covered.

## 5. Observations (no RETURN)

1. Ticket text says `s1_near_card`: "`2d+1` near blocks"; that is the `ℓ¹`/`zdistD` ball. The merged `STgexRHS` uses `zdistInf`, whose ball has `3^d` points; the file's `≤ 3^d` is the correct statement (T2079b). Dispatcher may fix the ticket wording; no statement change needed.
2. Section-7 helpers `hE_half`, `bulk_z0'`, `seqHflow_zero_sz0`, `s1xM_time_zero_sz0`, `s1Std_sz0(_const)`, `s1Setup_conStInd_const` are public (namespace `RBM.Ind.Step1SetupInst`, which carries the file stem); CLAUDE.md §3 (E) cosmetic only.
3. Merge note for the hub: the branch forked at `e84e0f7`; `main` has since added 3 lines to `RBM3D/Test/Axioms.lean` (`STStep2LocalPT`, `STStep2AvgPT`, `AdjacentMismatch`). Apply the branch's one-line hunk; taking the branch's whole file would drop them.
4. The prover's registry pre-check needs the full `lake build` first (stale `Test/Axioms` olean otherwise); its reported exit 0 is reproduced above.

## Verdict

| Target | Verdict |
|---|---|
| `Step1TargetV3` (d-form) + `stStep1_of_target` | PASS |
| `StochDomAt.of_subset_whp`, `of_subset_compl` (§26) | PASS |
| Elementary / Scales / F3–F8 / Generic / Loops / Bridge (58 public decls) | PASS |

**T2079: PASS.** No dispatcher sign-off needed.
