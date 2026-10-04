Auditor model: claude-opus-5-5

# T2163 audit (round 1): S5-27, initial term of Step 5, case (ii): `stIniTermII_holds`

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2163-audit1` (detached at `fc3a463` = `t/T2163`). Written at: Sun Oct  4 22:40:21 UTC 2026 (date -u).

## 1. Scope of the branch

```
$ git diff --name-only main...t/T2163
RBM3D/Induction/IniTermII.lean
RBM3D/Test/Axioms.lean
$ git diff main...t/T2163 -- RBM3D/Test/Axioms.lean   (the only hunk line)
-   `RBM.Gauss.Sizes.STIniTermII, -- initial term `(zYU2)`, case (ii); S5-01 (T2138, DECISIONS §40: owed)
```
Only the two sole writable files are touched; no merged file and no frozen signature changes.

## 2. Build and axioms (audit worktree)

```
$ lake build RBM3D.Induction.IniTermII ; echo exit=$?
Build completed successfully (3778 jobs).
exit=0
$ grep -E "error|IniTermII.lean:" build.log      # (no output)
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Induction/IniTermII.lean   # (no output; only linter set_options at :45-48)
$ lake env lean scratchpad/T2163/audit.lean ; echo exit=$?
'RBM.Gauss.Sizes.stIniTermII_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.iniTermII_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.iniTermII_core_same' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.iniTermII_concl' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step5Inst.iniTermII_core_inst' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step5Inst.iniTermII_core_same_inst' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step5Inst.iniTermII_concl_inst' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step5Inst.inst_iniTermII_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```
Public names (8): `iniTermII_core`, `iniTermII_core_same`, `iniTermII_concl`, `stIniTermII_holds`, and the four instances; every
private declaration carries the prefix `iniTermII_` (`grep -E "^private (theorem|def)" | grep -vc iniTermII_` → `0`). The hub runs the full build at merge.

## 3. Target 1: `stIniTermII_holds (d : ℕ) : STIniTermII d`

Statement check (`audit.lean`, compiled, exit 0 above):
```
example : (∀ d, STIniTermII d) = (∀ d, STIngR5 d STReg5II (fun sz E s t =>
    STIniTermConcl sz {0} STSigMixed E s t ∧ STIniTermConcl sz ∅ STSigSame E s t)) := rfl
example (d : ℕ) : STIniTermII d := stIniTermII_holds d
```
The pin (`Step5Pins.lean:331-333`) is used verbatim as the type; both conjuncts (`{0}`/`STSigMixed`, `∅`/`STSigSame`).
Proof (`IniTermII.lean:1718-1722`): `𝔠d := 1/100`, and of the `STIngR5` premises only `STFlow`, `0 ≤ s`, `t ≤ lemT z`, `STReg5II`
and `STDecay sz E s` are used, then `iniTermII_concl`. No added hypothesis; no structure with new fields (the only new `def`s are
the private kernels `iniTermII_PD`, `iniTermII_PI`, `iniTermII_Kf`). No cycle: the imports are the merged `Step5Pins`, `Step5Kit`,
`Step5Kernel`, `Prop5Hold`, `Prop5Short`, `Defs/RadialSum`, `Defs/Convolution`; `prop8ZeroMode_holds`, `prop5Short_holds`,
`step5Kernel_UN_decompU` are merged theorems, not hypotheses.
§29 (5)-(7): `STDecay` is taken at `s` only; `u` enters through `Ugen … (s n) u` and the scale `STprof sz n u D L` of the pin's
index (the `STIniTermConcl` body is the merged definition, not restated). (6): `|E| ≤ 2-κ` from `locDomain` + `abs_lemE_le`,
`t < 1` from `st5_t_lt_one`, `0 < lam ≤ 𝔡⁻¹` eventually from `WO` (`:1668-1683`).
**Instance**: `inst_iniTermII_proved := inst_iniTermII (stIniTermII_holds 3) Cd hCd` (`:1799-1803`) — exactly the instance the ticket
names (`Step5Pins.lean:980`, `szB, zB, 15/16, 31/32`, premises `szB_reg5II` compiled upstream). Compiles.
**Verdict target 1: PASS.**

## 4. Target 2: the deterministic cores

```
theorem iniTermII_core (d : ℕ) (Λ κm : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) (hκm : 0 < κm) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g W D E s u M lam : ℝ), 0 < g → g ≤ Λ → 0 < W →
        |E| ≤ 2 → κm ≤ (mE E).im → 0 ≤ s → s ≤ u → u < 1 → 1 - s ≤ g ^ 2 / (L : ℝ) ^ 2 → 0 ≤ M → 0 ≤ lam →
        ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ X : (Fin 2 → Zd d L) → ℂ,
          (∀ b, ‖X b‖ ≤ M * (lam * (W ^ d)⁻¹ * tailT d L g s (zdistInf d L (b 0 - b 1) : ℕ) + W ^ (-D))) →
          ∀ a, ‖zeroModeSet d L {0} (RBM.Ind.Ugen d L g E σ s u X) a‖ ≤
            C * M * (lam * (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ) +
              (1 - s) / (1 - u) * W ^ (-D))
```
`iniTermII_core_same` (`:1378`): same binders with `σ 0 = σ 1`, no `zeroModeSet`, floor `W ^ (-D)`.
Against the ticket's mathematics:
- `C = C(d, Λ, κm)` is chosen before `L, g, W, D, E, s, u, M, lam, σ, X, a`: constant before the data, as required.
- Input profile: `tailT d L g s r = BparamR … s r · exp(-√(r/ℓ_s))` (`Defs/Tail.lean:48`), i.e. `W^{-d}B_{s,r}e^{-√(r/ℓ_s)}` with a free
  prefactor `lam` (the lift sets `lam = Bctl_s^{1/5}`, which is the `STDecay` profile `Defs.lean:121-129`). Output `tailT` at `u`
  (untruncated `𝒯`; `tailW ≥` it, so stronger than with `𝒯̃`).
- Hypotheses: only `1-s ≤ g²/L²` from the regime (the lower bound `g²/L^d ≤ 1-u` is not assumed — weaker hypotheses).
- Deviation: the mixed core's floor is `((1-s)/(1-u))·W^{-D}`, not `W^{-D}`; the lift absorbs `ρ ≤ N ≤ W^{1/𝔠}` by taking
  `STDecay` at `D' = D + 1/𝔠` (`iniTermII_lift`, `:1567-1581`), so the pin is untouched. Covered by candidate `T2163b`.
- `Q^{(1)}𝒰^{(2)}X` is derived (`step5Kernel_UN_decompU` → `K ⊗ K`, `Q^{(1)}(K⊗K) = (K - ρL^{-d}J) ⊗ K`), not assumed; the
  paper's single term `(1-s)²Θ̊XΘ` is one of four (candidate `T2163a`).
**Instances** (`:1751-1790`): `iniTermII_core_inst`/`_same_inst` apply the cores with every hypothesis discharged by `norm_num`
at `d = 3, L = 4, g = 1, W = 2, D = 2, E = 1, s = 15/16, u = 31/32, Λ = 1, κm = 1/2, M = lam = 1`, `σ = (+,-)` / `(+,+)`, and the
nonzero tensor `X_b = W^{-3}𝒯_s(|b₁-b₂|) + W^{-2}`. The ticket's data `L = 3, g = 1/2` is outside regime (ii):
```
example : ¬ ((1:ℝ) - 15/16 ≤ (1/2)^2 / (3:ℝ)^2) := by norm_num                         -- compiles
example : (1:ℝ)^2/(4:ℝ)^3 ≤ 1 - 31/32 ∧ (1:ℝ) - 15/16 ≤ 1^2/(4:ℝ)^2 := by norm_num     -- compiles (szB data, L = 4, g = 1)
```
So no nondegenerate instance at the ticket's data exists for a core that carries the paper's regime bound; the substitute
`L = 4, g = 1` (the merged `szB` data, boundary `1-s = g²/L²`, `s < u`) is nondegenerate. Candidate `T2163c` records it.
**Verdict target 2: PASS** (both cores).

## 5. Target 3: `iniTermII_concl`

```
theorem iniTermII_concl {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ}
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (ht : ∀ n, t n ≤ lemT (z n))
    (hR : STReg5II sz s t) (hDec : STDecay sz (STflowE z) s) :
    STIniTermConcl sz {0} STSigMixed (STflowE z) s t ∧ STIniTermConcl sz ∅ STSigSame (STflowE z) s t
```
Every hypothesis is a premise of `STIngR5` (`Step5Pins.lean:82-93`); none added. Conclusion is the pin's conclusion verbatim.
**Instance**: `iniTermII_concl_inst` (`:1792`) at `(szB, zB, 15/16, 31/32)`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, with `flow_zB`,
`szB_flow_ht`, `szB_reg5II` (merged, compiled) discharging the deterministic hypotheses; only the stochastic induction input
`STDecay szB … (15/16)` stays a hypothesis (an `STIngR5` premise, i.e. another gate's conclusion). Compiles.
**Verdict target 3: PASS.**

## 6. Paper deltas

| Lean / paper difference | candidate |
|---|---|
| `(zYU2)` second term is one of four terms of `[(s/u)(I-L^{-d}J)+((u-s)/u)Θ̊_u] ⊗ [(s/u)I+((u-s)/u)Θ_u]`; `(u-s)/u ≤ 1-s` | `T2163a` |
| propagator time in `3_5:2275-2281` is `u` (paper writes `t`); output floor `ρW^{-D'}`, `D' = D + 1/𝔠` | `T2163b` |
| ticket instance data `L = 3, g = 1/2` outside regime (ii) | `T2163c` (ticket, not paper) |
| constants `C(d, Λ, κ_m)` instead of `C(d)` | `T2163d` |
`grep -n T2163 docs/paper-deltas.md` → no lines yet (the dispatcher appends). Every statement difference found above is covered.

## 7. Observations (no RETURN)

- Report (b) narrative item 5 and (a) row 10 differ on `D' = D + 1/𝔠` vs `D + 1/𝔠 + 1`; the report states the `+1` is unneeded. No statement effect.
- Private `iniTermII_zdistD_neg` duplicates public `zdistD_neg` (`Defs/Lattice.lean:103`); harmless.
- `iniTermII_core_same` carries `1 - s ≤ g²/L²`, which the report says is not mathematically needed; the pin's regime supplies it.
- Prove report: 252 lines (≤ 300).

## 8. Verdict

| target | verdict |
|---|---|
| 1 `stIniTermII_holds` | PASS |
| 2 `iniTermII_core`, `iniTermII_core_same` | PASS |
| 3 `iniTermII_concl` | PASS |

**T2163: PASS.** No dispatcher sign-off needed (the instance-data substitution is forced by the ticket's own regime and is recorded as `T2163c`).
At merge the hub adds `import RBM3D.Induction.IniTermII` after the last import line of `RBM3D.lean`.
