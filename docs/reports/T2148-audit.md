Auditor model: claude-opus-5-5

# T2148 audit (round 1): S5-28 `Induction/WardII` — `(zYU1)`, pin `STWardII`

Time: Sun Oct  4 17:59:39 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2148-audit1`, detached at `t/T2148` = `bf8a55b`; `main` = `37f3a22`.

## 1. Diff scope and registry

```
$ git diff --stat main...t/T2148
 RBM3D/Induction/WardII.lean | 364 ++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean      |   1 -
$ git diff main...t/T2148 -- RBM3D/Test/Axioms.lean
-   `RBM.Gauss.Sizes.STWardII, -- Ward identity `(zYU1)`, case (ii); S5-01 (T2138, DECISIONS §40: owed)
```
Only the two sole writable files; registry change is the single owed line the ticket names. No merged file (pins, frozen signatures) touched.

## 2. Build, axioms, hygiene

```
$ lake build RBM3D.Induction.WardII RBM3D.Test.Axioms
Build completed successfully (3778 jobs).     exit=0   (no warning/error line located in WardII.lean)
$ lake env lean ax.lean
'RBM.Gauss.Sizes.stWardII_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stWardII_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Induction/WardII.lean ; echo grep_rc=$?
grep_rc=1
$ lake env lean pre.lean     # import RBM3D; import RBM3D.Induction.WardII; #assert_rbm_axioms
axiom audit: 4506 theorems, 1606 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; ...
exit=0
$ git grep -n "stWardII_identity\|stWardII_holds\|wardII_" main -- RBM3D | grep -v Induction/WardII.lean ; echo rc=$?
rc=1                                                       (no name clash)
```
Imports: `Induction.Step5Cases`, `Induction.ConArgDet`, `Loop.KLWard` (all merged; not `RBM3D`). Helpers all `private wardII_*`.

## 3. Target 2 — `stWardII_holds (d : ℕ) : STWardII d`

Statement: the type is literally the merged pin `STWardII d` (`Step5Pins.lean:346`, unchanged by the diff):
```
def STWardIIConcl (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := STIdx2P sz STSigMixed s t)
    (fun n p ω => ‖STLKM … p.2.1.1 p.2.2 - zeroModeSet d (sz.L n) {0} (fun a' => STLKM … p.2.1.1 a') p.2.2‖)
    (fun n p _ => (STAI sz n)⁻¹ * (((sz.size n : ℕ) : ℝ) * etaT (E n) (p.1 : ℝ))⁻¹)
def STWardII (d : ℕ) : Prop := STIngR5 d STReg5II (fun sz E s t => STWardIIConcl sz E s t)
```
Against paper `3_5:2257-2262`: `(𝓛−𝒦)^{(2)} − Q^{(1)}∘(𝓛−𝒦)^{(2)} = Im(𝓛−𝒦)^{(1)}_{t,+,a₂}/(Nη_t) ≺ (λ²W^d)⁻¹/(Nη_t)`, σ₁ ≠ σ₂ — matches (`STSigMixed`, `Q^{(1)}` = `zeroModeSet {0}`, `N = (W L)^d` = `sz.size`, `A = STAI`), regime (ii) `STReg5II`. No hypotheses beyond the pin; no structure-field hypotheses.

Dependencies / no cycle: proof (`WardII.lean:269-330`) intros the `STIngR5` data and uses `STFlow` (|E|<2, t<1, eventual λ>0), `0 ≤ s`, `t ≤ lemT`, `STReg5II`, and `hS2.2.1 = STAvgU` from `STStep2Concl` (an upstream pin already a premise of `STIngR5`); merged lemmas `st5_t_lt_one`, `st5_eventually_A_ge_one`, `lemma28_quant`, `StochDomAt.precomp_param`, `st5_prec_mono`, plus target 1. No owed pin introduced; no new external hypothesis (limit check not owed). Axioms clean (§2).

Compiled nonempty instance (`WardII.lean:360-362`):
```
example (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STWardIIConcl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) Cd :=
  inst_wardII (stWardII_holds 3) Cd hCd
```
`inst_wardII` (merged, `Step5Pins.lean:986`) → `inst_ing5_II … szB_reg5II`: discharges `3 ≤ 3`, κ, ε, 𝔡 > 0, `STFlow szB … zB`, `0 ≤ s`, `s < t`, `t ≤ lemT`, regime (ii) (`1−t = 1/32 ≥ 1/64 = λ²/L³`, `1−s = 1/16 ≤ λ²/L²`, `L = 4`, `W_n = n+4`) and `STConStInd`; only the stochastic pins of other gates (`STKbound … STLKU`) remain hypotheses of `InstIng5Concl`. Nondegenerate (window `[15/16, 31/32]` nonempty, `N = (4(n+4))³`). Compiles (§2 build).

Verdict target 2: **PASS**.

## 4. Target 1 — `stWardII_identity`

```
$ #check @RBM.Gauss.Sizes.stWardII_identity
∀ {d : ℕ} (sz : RBM.Gauss.Sizes d) (n : ℕ) {E u : ℝ}, |E| < 2 → 0 ≤ u → u < 1 →
  ∀ {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}, H.IsHermitian →
  ∀ {σ : Fin 2 → Bool}, σ 0 ≠ σ 1 → ∀ (a : Fin 2 → RBM.Zd d (sz.L n)),
    sz.STLKM n E u H σ a - RBM.zeroModeSet d (sz.L n) {0} (fun a' => sz.STLKM n E u H σ a') a =
      ↑(sz.STLKM n E u H (fun x => true) fun x => a 1).im / (↑(sz.size n) * ↑(RBM.Gauss.etaT E u))
```
Against the ticket's item 1 (`± Im((𝓛−𝒦)^{(1)}_{u,+,a₂})/(Nη_u)`, deterministic, every Hermitian `H`, both mixed σ): the sign is `+` for both σ, as printed in `(zYU1)` (`3_5:2259`). `STLKM` = `STLM − STKloop` (`Step2Defs.lean:68`); `zeroModeSet {0}` = `Q^{(0)}` on the first index (`Kernel/Evolution.lean:190-200`, `avgOp` = `(L^d)⁻¹ Σ_c`); `size n = (W n · L n)^d` (`Defs/Sizes.lean:157`); `etaT E u = (1−u) Im m(E)` (`Loop/GLoop.lean:75`). Side conditions `|E|<2`, `0≤u<1`, Hermitian `H` are the paper's implicit setting (proposed as delta T2148a). Fully general in `d`, `sz`, `n`, `a`, both σ; not a special case.

Compiled nonempty instance (`WardII.lean:331-357`): `wardII_szI : Sizes 3` with `L = 3`, `W = 1`, `λ = 1`; `E = 0`, `u = 1/2`, `H = 1` (27×27, `Matrix.isHermitian_one`), `σ = ![true,false]`, `a = (0, e₁)`; hypotheses discharged by `norm_num`, `norm_num`, `norm_num`, `Matrix.isHermitian_one`, `decide`. Matches the ticket's required instance `d = 3, L = 3, W = 1`. Compiles (§2).

Verdict target 1: **PASS**.

## 5. Paper deltas

Prove report (d) proposes `T2148a` (sign `+` for both mixed σ; deterministic side conditions `H` Hermitian, `|E|<2`, `0≤u<1`) and `T2148b` (`Δ_u ≍ A⁻¹` used only as `W^{-d}B_{u,0} ≤ 2A⁻¹`, constant absorbed in `≺`). These cover every Lean/paper difference found above. Not yet in `docs/paper-deltas.md` (dispatcher appends).

## 6. Observations (no effect on verdict)

- Report (c) says "Names verified absent: none searched for" — acceptable.
- The prove report's (a) row 6 constant-2 slack computation was not re-run; it is checked by Lean (`wardII_Bctl_le` compiles axiom-clean).

## Verdict

T2148: **PASS** (both targets). No dispatcher sign-off needed.
