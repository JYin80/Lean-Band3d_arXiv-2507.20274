Auditor model: claude-opus-5-5

# T2400 audit (round 1) — BA-G3b `BA/GreenStab.lean` — Sun Oct 11 00:57:26 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2400-audit1`, detached at `t/T2400` = `8403a83`
(merge-base with main `d859e60`; main now `cbda0ab`). `$S` = auditor scratchpad `T2400/`.

## 1. Diff scope (sole writable files)
```
$ git diff --name-only main...t/T2400
RBM3D.lean
RBM3D/BA/GreenStab.lean
RBM3D/BA/Prop6Path.lean
$ git diff -U0 main...t/T2400 -- RBM3D/BA/Prop6Path.lean RBM3D.lean | grep -E '^[-+][^-+]'
+import RBM3D.BA.GreenStab
-private lemma baP8_BATheta_shift (g E : ℝ) (m : ℂ) (t : ℝ) (σ₁ σ₂ : Bool) (a b r : Zd d L) :
+lemma baP8_BATheta_shift (g E : ℝ) (m : ℂ) (t : ℝ) (σ₁ σ₂ : Bool) (a b r : Zd d L) :
```
Prop6Path: only the word `private` removed (ticket option (ii)); signature unchanged. Stop line: 442 + 0 net < 1,000.

## 2. Build, hygiene, axioms
```
$ lake build RBM3D.BA.GreenStab 2>&1 | grep -E "error|declaration uses|Build completed|sorry"
Build completed successfully (3756 jobs).
$ grep -nE "sorry|admit|native_decide|^ *axiom " RBM3D/BA/GreenStab.lean | wc -l
       0
$ lake env lean $S/audit.lean     # (#print axioms part)
'RBM.BA.baStab_of_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baM_row_l1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baM_col_l1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baM_rho2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baM_rhohat' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMfine_rhohat' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baTheta_weighted_l1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baP8_BATheta_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenStabInst.inst_baStab' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenStabInst.inst_col_l1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenStabInst.inst_rho2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenStabInst.inst_rhohat' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenStabInst.inst_rhohat_fine' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenStabInst.inst_theta_weighted' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenStabInst.inst_theta_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```
Name clash against current main (`cbda0ab`, includes merged T2390 GreenCore):
```
$ for n in baStab_of_real baM_row_l1 baM_col_l1 baM_rho2 baM_rhohat baMfine_rhohat baTheta_weighted_l1 GreenStab_clam GreenStab_CTheta GreenStabInst ...; do git grep -wc $n main -- RBM3D RBM3D.lean | wc -l; done
all 0
```

## 3. Target (S1) `baStab_of_real` — statement vs the merged `BAStab` (now on main)
`BAStab` was merged with T2390 (`main:RBM3D/BA/GreenCore.lean:1268-1271`). The auditor copied that text verbatim by
`git show main:RBM3D/BA/GreenCore.lean | sed -n 1268,1271p` (renamed `AuditBAStab`) into `$S/audit.lean` and compiled
the ticket's one-line link against the branch module:
```
def AuditBAStab (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (t K : ℝ) : Prop :=
  ∀ (v : Zd d L → ℂ) (B : ℝ),
    (∀ a, ‖v a - (t : ℂ) * ∑ b, BAMss d L (BAMB d L g (E : ℂ) m) true true a b * v b‖ ≤ B) →
      ∀ a, ‖v a‖ ≤ K * B
example (d L : ℕ) [NeZero L] (g κ E : ℝ) (m : ℂ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : AuditBAStab d L g E m t (16 * κ⁻¹ ^ 4) :=
  fun v B h a => baStab_of_real d L g κ E m hκ hr t ht0 ht1 v B h a
-- lake env lean $S/audit.lean : no error lines, exit 0
```
Hypotheses exactly as pinned (`BAReal`, `0 < κ`, `0 ≤ t ≤ 1`); `K = 16 κ⁻⁴` has no `g`, `Λ`, `L`. Hidden hypotheses:
```
def RBM.BA.BAReal := fun d L [NeZero L] g κ E m => BASelf d L g (↑E) m ∧ κ ≤ m.im
def RBM.BA.BASelf := fun d L [NeZero L] g z m => 0 < m.im ∧ m = (↑(L ^ d))⁻¹ * (BAMB d L g z m).trace
```
Plain Props, both inhabited at the instance datum (§6). **PASS.**

## 4. Targets (S3) row facts of `M` — statements (from the file, lines 116-213)
- `baM_col_l1` (`ρ = sup_c Σ_b |M_bc|`): `∑ b, ‖BAMB d L g E m b c‖ ≤ (BAct_rate d Λ κ)⁻¹ * expC (d-2) (BAct_rate d Λ κ)`,
  under `2 ≤ d, 3 ≤ L, 0 < Λ, 0 < g ≤ Λ, 0 < κ, BAReal`. Same bound as merged `BAMB_row_l1` (rows), transferred by
  `BAMB_symm`; uniform in `L`. (`baM_row_l1` = `BAMB_row_l1` for general `2 ≤ d`.)
- `baM_rho2` (`ρ₂ ≤ 1`): `∑ b, ‖M a b‖ * ‖M b c‖ ≤ 1` for all `a c`, under `BASelf` only (weaker than the ticket's
  `BAReal`; `BAReal → BASelf` is `.1`, so the target is a strengthening, not a special case).
- `baM_rhohat` (`ρ̂`, `ν = c₀/2`): `∑ b, ‖M a b‖ * exp(c₀/2 · |a-b|) ≤ c₀⁻¹ * expC (d-2) (c₀/2)`, `c₀ = BAct_rate d Λ κ`:
  matches the ticket's `ρ̂ ≤ c₀⁻¹ S_{c₀/2}`. `baMfine_rhohat` is the same on the fine lattice with block distance.
Ticket line "ρ … from `BAMfine_row_l1` / `BAMB_row_l1`": the block column bound is delivered; the fine-lattice row ℓ¹
is the already-merged `BAMfine_row_l1` (not restated). Ticket item 2 asks for the `M^{(B)}` facts; satisfied. **PASS.**

## 5. Target (S2) `Θ` facts
- Shift: `baP8_BATheta_shift` made public in place (§1); statement `Θ_t(a+r, b+r) = Θ_t(a, b)` unchanged.
- `baTheta_weighted_l1`: `∑ a', ‖BATheta d L g E m t σ σ b a'‖ * exp(2 c_λ |b - a'|) ≤ GreenStab_CTheta d Λ κ` with
  `GreenStab_clam = min (BAct_rate/12) (BAp5s_rate/6)` (= `c_λ = min(c₀/12, μ/6)`) and
  `GreenStab_CTheta = BAp5s_C * (1 + Λ^2 * expC (d-2) (2*BAp5s_rate/3))` (= `C₅(1 + Λ² S_{2μ/3})`), all `σ`, all `b`,
  `0 ≤ t ≤ 1`, uniform in `L`. Exactly the ticket's (S2) formula.
- Input used is `baProp5s_of_real` (explicit `C₅ = BAp5s_C`, `μ = BAp5s_rate`), not `baProp5s_holds` (`∃ C c`) named
  in the ticket; the report's (a) records this correction. Merged signature (`#check`):
```
baProp5s_of_real : ∀ (d L : ℕ) [NeZero L], 3 ≤ L → 2 ≤ d → ∀ (Λ g κ E : ℝ) (m : ℂ), 0 < Λ → 0 < g → g ≤ Λ → 0 < κ →
  BAReal d L g κ E m → ∀ (t : ℝ), 0 ≤ t → t ≤ 1 → ∀ (σ : Bool) (a : Zd d L),
  ‖BATheta d L g E m t σ σ 0 a‖ ≤ BAp5s_C d Λ κ * ((if a = 0 then 1 else 0) + g ^ 2 * Real.exp (-BAp5s_rate d Λ κ * ↑(zdistD d L a)))
```
  A merged theorem, so no external hypothesis and no cycle (GreenStab imports only Prop5Short, Prop6Path, Ward,
  GreenSchur, CombesThomas; none imports GreenStab). **PASS.**

## 6. Compiled nonempty instances (`namespace GreenStabInst`, lines 328-440)
Datum: `d = 3`, `sz0` at `n = 0`, `L = sz0.L 0 = 4`, `W = 32`, `κ = 1/2`, `Λ = 1`, `t = 1/2`, `σ = true`.
```
def RBM.Gauss.SizesInst.sz0 : Sizes 3 := { L := fun n => 4 * (n + 1), W := fun n => (2 * (n + 1)) ^ 5,
    lam := fun n => ((2 * (↑n + 1)) ^ 6)⁻¹, ... }
FlowPinsInst.flow_sz0 : BAFlow Gauss.SizesInst.sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) FlowPinsInst.zSeq
'RBM.BA.FlowPinsInst.flow_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
```
- `hr0I : BAReal 3 (sz0.L 0) g0I (1/2) E0I m0I := BAflow_real … flow_sz0 0` — a merged theorem, not a hypothesis.
- `g0I_pos : 0 < g0I`, `g0I_le : g0I ≤ 1/64` proved; `g ≤ Λ = 1` discharged.
- `inst_baStab`: applies `baStab_of_real` to `vI = δ_0` (`vI_zero : vI 0 = 1`, nonzero), `B = 3/2`; the hypothesis
  `‖vI a - ½ Σ_b M⁺⁺_{ab} vI b‖ ≤ 3/2` is proved (Ward, `Q_le_one`); conclusion `‖vI a‖ ≤ 384`. Nondegenerate.
- `inst_col_l1`, `inst_rho2`, `inst_rhohat`, `inst_rhohat_fine`, `inst_theta_weighted`, `inst_theta_shift`: each
  applies its target at the datum with every hypothesis discharged (`by norm_num`, `sz0.three_le_L 0`, `g0I_pos`,
  `g0I_le`, `hr0I`); no open hypothesis, no `N = 0`, no empty index (`card Zd 3 4 = 64`), no `False` premise.
All compile (build §2) with the standard three axioms. **PASS.**

## 7. Paper deltas
Lean/paper differences and their coverage in the prove report (d):
| Difference | Candidate |
|---|---|
| (S1) explicit `K = 16 κ⁻⁴ = ε⁻²` via max principle, not in the paper (`A_deterministic_estimates.tex:28-41`) | `T2400a` |
| explicit `c_λ`, `C_Θ̂ = C₅(1+Λ² S_{2μ/3})`, `ρ̂ ≤ c₀⁻¹ S_{c₀/2}`, `ρ₂ ≤ 1` | `T2400b` (ρ₂ ≤ 1 is the Ward identity, no delta needed) |
| `3 ≤ d` used as `2 ≤ d` | `T2400c` |
All statement differences are covered.

## 8. Observations (no RETURN)
- O1. Main has moved to `cbda0ab` (T2390 merged, adds `import RBM3D.BA.GreenCore` to `RBM3D.lean`); the branch's
  `RBM3D.lean` import line will conflict textually. Per CLAUDE.md §3 (A) step 4 the hub adds the import itself after the
  last `import` line; bring in only `GreenStab.lean` and `Prop6Path.lean` from the branch.
- O2. The ticket's G4 link (`BAStab … (16 κ⁻⁴)` from `baStab_of_real`) compiles against the now-merged `BAStab`
  text (§3), so G4's one-line link should go through without conversion.
- O3. The ticket cites `baProp5s_holds`; the proof correctly uses `baProp5s_of_real` (explicit constants). Dispatcher
  may update the ticket wording; no statement effect.

## Verdict
| Target | Verdict |
|---|---|
| (S1) `baStab_of_real` | PASS |
| (S3) `baM_col_l1` / `baM_row_l1`, `baM_rho2`, `baM_rhohat`, `baMfine_rhohat` | PASS |
| (S2) `baP8_BATheta_shift` (public), `baTheta_weighted_l1` | PASS |
| Instances, build, axioms, diff scope, paper deltas | PASS |

**T2400: PASS.** No dispatcher sign-off needed.
