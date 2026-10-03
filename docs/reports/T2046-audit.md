Auditor model: claude-opus-5-5
# T2046 audit (round 1) — S1-15 `RBM3D/Green/Stability.lean` — Sat Oct  3 10:22:16 UTC 2026

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2046-audit1` (detached at t/T2046 = d46b4ec). Targets (ticket + ST1-COMMON item 6): the RBM2D@c9a24cf public declarations `Kstab2`→`Kstab3`, `stable_svar`, `stable_svar_bulk`, `eventually_Kstab2_mul_rpow_le`→`eventually_Kstab3_mul_rpow_le`; additions `stable_svar_vtx`, `stable_svar_bulk_vtx`, `one_le_Kstab3`, `eventually_stable_svar_bulk`.

## 1. Statement vs pin (RBM2D@c9a24cf after R1–R4, class c rewrite of the constant)
```
$ python3 sdiff.py   # RBM2D statements renamed (R1-R4, spectralM→mE, Filter.atTop→atTop), token diff vs RBM3D
== stable_svar -> stable_svar
   identical after renaming
== stable_svar_bulk -> stable_svar_bulk
   insert RBM2D:  | RBM3D: (hd : 3 ≤ d)
   replace RBM2D: {κ | RBM3D: {Λ κ
   insert RBM2D:  | RBM3D: (hg : 0 < g) (hgΛ : g ≤ Λ)
   replace RBM2D: (Kstab2 κ L) | RBM3D: (Kstab3 d Λ κ)
== eventually_Kstab2_mul_rpow_le -> eventually_Kstab3_mul_rpow_le
   replace RBM2D: {κ 𝔠 | RBM3D: (Λ κ : ℝ) {𝔠
   delete RBM2D: (hκ : 0 < κ) | RBM3D: 
   replace RBM2D: Kstab2 | RBM3D: Kstab3 d Λ
   delete RBM2D: (sz.L n) | RBM3D: 
$ git -C ../RBM2D show c9a24cf:RBM2D/Green/Stability.lean | sed -n 40,42p
noncomputable def Kstab2 (κ : ℝ) (L : ℕ) : ℝ :=
  1 + 2 * (180 * 40002 ^ 2) / RBM.KLoop.gapK κ *
    (1 + 40000 / Real.sqrt (RBM.KLoop.gapK κ)) ^ 2 * (1 + Real.log L)
$ sed -n 212,214p RBM3D/Green/Stability.lean
noncomputable def Kstab3 (d : ℕ) (Λ κ : ℝ) : ℝ :=
  1 + pin5sC d Λ (Real.sqrt (κ * (4 - κ)) / 2) *
    (1 + Λ ^ 2 * expC (d - 2) (pin5sc d Λ (Real.sqrt (κ * (4 - κ)) / 2)))
$ grep -n -A8 "def Prop5Short" RBM3D/Propagator/Pins.lean   (pin 5s, proved by prop5Short_holds, Prop5Short.lean:400)
def Prop5Short (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
        ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ σ : Bool, ∀ a : Zd d L,
          haveI : NeZero L := ⟨by omega⟩
          ‖Theta d L g ((t : ℂ) * (PropSpin m σ * PropSpin m σ)) 0 a‖
            ≤ C * ((if a = 0 then (1 : ℝ) else 0) + g ^ 2 * Real.exp (-c * (zdistD d L a : ℝ)))
```
Assessment.
- `stable_svar`: identical to the pin after renaming (PASS). `stable_svar_vtx` is the same statement on `Vtx d L W` with the merged `svar`; `stable_svar` is derived from it through `splitEquiv`.
- `stable_svar_bulk`: residual differences `+ (hd : 3 ≤ d)`, `+ Λ`, `+ (hg : 0 < g) (hgΛ : g ≤ Λ)`, `Kstab2 κ L → Kstab3 d Λ κ`. RBM2D's profile has no coupling; RBM3D's `svarF d L W g` has one, and the window `0 < g ≤ Λ` is exactly the hypothesis of pin 5s (above) and is satisfied by `(eq:WO)` (`W^{-d/2+𝔡} ≤ λ ≤ 𝔡⁻¹`; used in `eventually_stable_svar_bulk`, `Λ = 𝔡⁻¹`). This is the class-c rewrite the ticket asks for. Uniformity: `t ∈ [0,1)`, `|E| ≤ 2-κ`, all `L ≥ 3`, all `W ≥ 1`; the constant is quantified before `L, g, t, E` (it depends on `(d, Λ, κ)` only), so the statement is stronger than RBM2D's in `L` (no `1 + log L`).
- `Kstab3`: a `def` (not `∃ K`) built from the chosen constants of the **proved** `prop5Short_holds` (private `pin5sC`/`pin5sc`, `Classical.choose`, falling back to `1` off the domain `3 ≤ d ∧ 0 < Λ ∧ 0 < κ`) and the merged `expC`. On the domain, `pin5s_spec` (private, `Stability.lean:241`) re-extracts the spec; `one_le_Kstab3` holds for all inputs. The ticket's questions ("give the `d`-dimensional constant", "does `log L` survive at `d = 3`") are answered: `Kstab3 = 1 + C_s(1 + Λ² expC(d-2, c_s))`, no `L`; the `log L` of `(eq:latticesum_d3)` is not used. Mathematical check of the route: `Σ_b|Θ(a,b)| = Σ_x|Θ(0,x)|` (translation invariance) `≤ C_s(1 + g² Σ_x e^{-c_s|x|}) ≤ C_s(1 + Λ² expC)` (`stability_rowsum_le`, line 268), then `‖v‖∞ ≤ (1 + KΘ)B` — correct; `κ'' = √(κ(4-κ))/2 ≤ Im m_E(E)` on `|E| ≤ 2-κ` (`stability_bulkIm_le`, line 306) since `4 - E² ≥ 4 - (2-κ)² = κ(4-κ)`.
- `eventually_Kstab3_mul_rpow_le`: R1; `hκ` dropped (unused in RBM2D, `have _ := hκ`): fewer hypotheses; `Λ κ` explicit because `Kstab3` depends on them; `(sz.L n)` gone because `Kstab3` has no `L`. Same quantifier order (fixed `Λ κ 𝔠 c` before `∀ᶠ n`). PASS.
- `eventually_stable_svar_bulk` (addition): takes `Admissible 𝔠 𝔡`, conclusion at `Λ = 𝔡⁻¹`, fixed parameters before `∀ᶠ n`, then `∀ E t`. PASS.

## 2. Vacuity, hidden hypotheses, cycles
```
$ sed -n 911,912p RBM3D/Green/EntryCore.lean      # the predicate (merged S1-10), a plain def, no structure
def Stable (S : n → n → ℝ) (ξ : ℂ) (K : ℝ) : Prop :=
  ∀ (v : n → ℂ) (B : ℝ), (∀ i, ‖v i - ξ * ∑ k, (S i k : ℂ) * v k‖ ≤ B) → ∀ i, ‖v i‖ ≤ K * B
$ sed -n 6,10p RBM3D/Green/Stability.lean         # imports: merged modules only, not RBM3D, no ST-2..6 file
import RBM3D.Green.EntryCore
import RBM3D.Propagator.Prop5Short
import RBM3D.Defs.RadialSum
import RBM3D.Gauss.FineModel
import RBM3D.Defs.Semicircle
$ lake env lean ax.lean | (signatures of the merged inputs used)
@RBM.sum_radial_exp_decay_le : ∀ {L : ℕ} [inst : NeZero L] (k : ℕ) {c : ℝ},
  0 < c → ∑ x, Real.exp (-(c * ↑(RBM.zdistD (k + 2) L x))) ≤ RBM.expC k c
@RBM.sum_norm_Theta_row_le : ∀ {d L : ℕ} [inst : NeZero L] {g : ℝ},
  3 ≤ L → ∀ {t : ℝ}, 0 ≤ t → t < 1 → ∀ {m : ℂ}, ‖m‖ = 1 → ∀ (a : RBM.Zd d L), ∑ b, ‖RBM.Theta d L g (↑t * m) a b‖ ≤ (1 - t)⁻¹
RBM.Gauss.SizesInst.sz0_admissible : RBM.Gauss.SizesInst.sz0.Admissible (1 / 6) (1 / 10)
```
No target takes a premise-type hypothesis: the only non-deterministic-looking input, pin 5s, enters through the theorem `prop5Short_holds` (merged), not as a hypothesis; `STKbound` is not used. No hypothesis sits in a structure field (`Stable` is the conclusion; `Sizes.Admissible` is the merged R1 size condition, discharged at `sz0`). No cycle: imports are merged files; nothing imports `Green/Stability`. No external hypothesis, so no limit check is required. **PASS.**

## 3. Compiled nonempty instances (`Stability.lean` §Checks, lines 403-457; compiled in the build of §4)
```
407:/-- `stable_svar_vtx` at `ξ = (1/2) m(1)`, `‖ξ‖ = 1/2 < 1`, with the row-sum bound
410:example : Stable (svar 3 4 32 (1 / 64)) (((1 / 2 : ℝ) : ℂ) * mE 1) (1 + (1 - (1 / 2 : ℝ))⁻¹) :=
411:  stable_svar_vtx (W := 32) (g := 1 / 64) (by norm_num)
416:/-- `stable_svar` at the same data, on the fine lattice `Z_{128}^3`. -/
417:example : Stable (svarF 3 4 32 (1 / 64)) (((1 / 2 : ℝ) : ℂ) * mE 1) (1 + (1 - (1 / 2 : ℝ))⁻¹) :=
418:  stable_svar (W := 32) (g := 1 / 64) (by norm_num)
423:/-- `stable_svar_bulk_vtx` at `d = 3`, `L = 4`, `W = 32`, `g = 1/64 ≤ Λ = 10`, `κ = 1/2`, `E = 1`,
426:example : Stable (svar 3 4 32 (1 / 64)) (((9 / 10 : ℝ) : ℂ) * mE 1 ^ 2) (Kstab3 3 10 (1 / 2)) :=
427:  stable_svar_bulk_vtx (W := 32) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
430:/-- `stable_svar_bulk` at the same data, on the fine lattice. -/
431:example : Stable (svarF 3 4 32 (1 / 64)) (((9 / 10 : ℝ) : ℂ) * mE 1 ^ 2) (Kstab3 3 10 (1 / 2)) :=
432:  stable_svar_bulk (W := 32) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
436:example : 1 ≤ Kstab3 3 10 (1 / 2) := one_le_Kstab3 3 10 (1 / 2)
438:/-- `eventually_Kstab3_mul_rpow_le` along `sz0` (`SizeTendsto`, `Bandwidth (1/6)`), `c = 1/2`. -/
439:example : ∀ᶠ n in atTop,
441:  eventually_Kstab3_mul_rpow_le sz0 10 (1 / 2) (𝔠 := 1 / 6) (c := 1 / 2) (by norm_num)
444:/-- `eventually_stable_svar_bulk` along `sz0`, admissible at `𝔠 = 1/6`, `𝔡 = 1/10`
446:example : ∀ᶠ n in atTop, ∀ E t : ℝ, |E| ≤ 2 - 1 / 2 → 0 ≤ t → t < 1 →
449:  eventually_stable_svar_bulk sz0 (by norm_num) sz0_admissible (by norm_num)
452:example : ∃ n : ℕ, ∀ E t : ℝ, |E| ≤ 2 - 1 / 2 → 0 ≤ t → t < 1 →
455:  (eventually_stable_svar_bulk sz0 (by norm_num) sz0_admissible (by norm_num)).exists
```
Data: `d = 3`, `L = 4`, `W = 32`, `g = 1/64`, `Λ = 10`, `κ = 1/2`, `E = 1`, `t = 9/10` (bulk) / `ξ = (1/2) m_E(1)` (row-sum form, `KΘ = (1-1/2)⁻¹` discharged by the merged property-4 lemma, not assumed); sequence `sz0` (`SizeTendsto`, `Bandwidth (1/6)`, `Admissible (1/6) (1/10)`, all merged theorems). Every hypothesis is discharged by `norm_num` or a merged lemma; no `N = 0`, empty index, collapsed window or `False` premise (`|1| ≤ 3/2`, `0 < 1/64 ≤ 10`, `9/10 < 1`, `L = 4 ≥ 3`). All 8 public declarations have an instance (the `∀ᶠ` one is also made concrete by `.exists`). `Kstab3 3 10 (1/2)` is a fixed constant in the conclusion, not a witness that makes a hypothesis hold. **PASS.**

## 4. Build, axioms, hygiene, scope
```
$ lake build RBM3D.Green.Stability   (audit worktree; error/warning/summary lines)
✔ [3297/3297] Built RBM3D.Green.Stability (3.3s)
Build completed successfully (3297 jobs).
exit 0
$ (cd RBM3D-wt/T2046-audit1 && lake env lean ax.lean)   (#print axioms of the 8 public declarations)
'RBM.Green.stable_svar_vtx' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.stable_svar' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.Kstab3' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.one_le_Kstab3' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.stable_svar_bulk_vtx' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.stable_svar_bulk' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.eventually_Kstab3_mul_rpow_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.eventually_stable_svar_bulk' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^ *axiom " RBM3D/Green/Stability.lean
rc=1 (1 = no match)
$ git diff main...t/T2046 --name-only
RBM3D/Green/Stability.lean
$ git rev-parse --short main t/T2046; git merge-base main t/T2046
main=3747ff7 branch=d46b4ec merge-base=d9de66f
$ for n in <8 public names>; git grep -nw $n main -- RBM3D RBM3D.lean | wc -l
stable_svar_vtx 0
stable_svar 0
Kstab3 0
one_le_Kstab3 0
stable_svar_bulk_vtx 0
stable_svar_bulk 0
eventually_Kstab3_mul_rpow_le 0
eventually_stable_svar_bulk 0
$ lake env lean pre.lean   (import RBM3D; import RBM3D.Green.Stability; #assert_rbm_axioms) — exit 0
axiom audit: 1484 theorems, 543 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 28 (borrowed 2, owed 14, structural 12).
registry: 5 borrowed + 19 owed + 23 structural; 19 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
```
Build passes, only the three standard axioms, no forbidden token, scope = the one sole writable file (`RBM3D/Test/Axioms.lean` untouched), no new public name on current `main` (3747ff7), no frozen signature touched (new file only). Unpinned helpers are `private` (§3 (E)). **PASS.**

## 5. Paper deltas
Lean/paper differences and their coverage (prove report (d)):
- constant depends on `(d, Λ, κ)` and the bound is stated on `0 < g ≤ Λ` (paper: "constants depending on `d` and `κ`", `(prop:ThfadC_short)`, `1_2:1147`) → **T2046a** (same convention as the T2003 pins).
- `κ'' = √(κ(4-κ))/2` passed to pin 5s for the domain `|E| ≤ 2-κ` (paper uses one letter `κ`) → **T2046b**.
- `3 ≤ d`: the paper's standing assumption, no delta. Non-explicit `Kstab3` (chosen pin-5s constants): a Lean-vs-RBM2D difference (RBM2D's `Kstab2` is explicit), not a paper difference (the paper's constants are unspecified). Covered.

## Observations (no statement, instance, build, axiom or delta effect)
- O-1. With the new module, the registry scan lists `RBM.Green.Stable` among "carry nothing" premises (structural found 13 → 12): `stable_svar*` conclude `Stable`. A certificate entry is a dispatcher matter (prove report narrative 9, O2).
- O-2. `Kstab3` has no closed form in Lean; the numeric values in section (a) (4.6e22, 2.4e11) evaluate the docstring formula of `prop5Short_holds`, not a Lean-checked value (the prove report says so).
- O-3. `main` advanced to 3747ff7 after the branch base d9de66f; `git diff main...t/T2046` still touches only `RBM3D/Green/Stability.lean`; the hub's full build at merge decides.

## Verdict
| target | statement | vacuity/hidden/cycle | instance | build/axioms | deltas | verdict |
|---|---|---|---|---|---|---|
| `stable_svar` / `stable_svar_vtx` | identical after renaming | none | yes | ok | none needed | PASS |
| `Kstab3`, `one_le_Kstab3` | class-c `d ≥ 3` constant, `(d,Λ,κ)` only | built on proved pin 5s | yes | ok | T2046a/b | PASS |
| `stable_svar_bulk` / `_vtx` | pin + `3 ≤ d`, `0 < g ≤ Λ` (pin-5s window) | none | yes | ok | T2046a/b | PASS |
| `eventually_Kstab3_mul_rpow_le` | pin, `hκ` dropped, no `L` | none | yes (`sz0`) | ok | none needed | PASS |
| `eventually_stable_svar_bulk` | addition under `Admissible`, `Λ = 𝔡⁻¹` | none | yes (`sz0`, `.exists`) | ok | T2046a | PASS |

**Overall: PASS.** No dispatcher sign-off needed.
