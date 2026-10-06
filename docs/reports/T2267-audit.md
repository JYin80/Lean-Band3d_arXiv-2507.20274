Auditor model: claude-opus-5-5

# T2267 audit (UN-20, `RBM3D/Universality/JakKernel.lean`), round 1 — Tue Oct  6 07:40:05 UTC 2026

Branch `t/T2267` at 9e9a4bf (merge-base 8bb6f82); audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2267-audit1` (detached).
Scratch files: `<scratchpad>/T2267/` (not committed).

## 1. Scope (`git diff main...t/T2267`)

```
$ git diff --stat main...t/T2267
 RBM3D/Universality/JakKernel.lean | 1092 +++++++++++++++++++++++++++++++++++++
 1 file changed, 1092 insertions(+)
$ grep -n "^import" RBM3D/Universality/JakKernel.lean
6:import RBM3D.Universality.JakSpectral
7:import Mathlib.Algebra.Order.Floor.Semiring
8:import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
```
The only file is the sole writable file. `Axioms.lean` is untouched, as expected. No merged file is edited, so no frozen signature changes. The imports are those the ticket allows; there is no `Green/*`, `InjSum` or `Main/*` import.

## 2. Build and axioms (audit worktree)

```
$ lake build RBM3D.Universality.JakKernel   # error/warning lines + tail
warning: RBM3D/Defs/Tail.lean:169:100: This line exceeds the 100 character limit ...   (3 lines, merged file, not this ticket)
Build completed successfully (3330 jobs).
exit 0
$ grep "JakKernel.lean.*depends on axioms" build.log   (11 lines, all identical axiom set)
'RBM.Univ.im_Gres_apply_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.sum_mass_window_le_im_green' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.sum_mass_window_le_of_im_green_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.jak_pointwise_good' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.jak_pointwise_crude' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.JakKernelInst.im_Gres_le_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.JakKernelInst.gridGood_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.JakKernelInst.blockM_le_432' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.JakKernelInst.inst_window' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.JakKernelInst.inst_good' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.JakKernelInst.inst_crude' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Universality/JakKernel.lean
(no output)
```
The build log has no warning or error line for `JakKernel.lean`.

## 3. Statements against the pin (check file sections 2.1–2.4)

The scratch file `scratch2.lean` contains `import RBM3D.Universality.JakKernel`, then check lines 101..218 (sections 2.2–2.4) copied verbatim, without check 2.1. As a result, `jakGridGood` in the pinned bodies resolves to the library's `RBM.Univ.jakGridGood`. Then follows:
```
example : T2267_im_Gres_apply_self := @RBM.Univ.im_Gres_apply_self
example : T2267_sum_mass_window_le_im_green := @RBM.Univ.sum_mass_window_le_im_green
example : T2267_sum_mass_window_le_of_im_green_le := @RBM.Univ.sum_mass_window_le_of_im_green_le
example : T2267_jak_pointwise_good := @RBM.Univ.jak_pointwise_good
example : T2267_jak_pointwise_crude := @RBM.Univ.jak_pointwise_crude
example : T2267_H1 = RBM.Univ.JakKernelInst.H1 := rfl
example : T2267_y0 = RBM.Univ.JakKernelInst.y0 := rfl
example : T2267_im_Gres_le_inv := @RBM.Univ.JakKernelInst.im_Gres_le_inv
example : T2267_gridGood_one := @RBM.Univ.JakKernelInst.gridGood_one
example : T2267_blockM_le_432 := @RBM.Univ.JakKernelInst.blockM_le_432
example : T2267_inst_window := @RBM.Univ.JakKernelInst.inst_window
example : T2267_inst_good := @RBM.Univ.JakKernelInst.inst_good
example : T2267_inst_crude := @RBM.Univ.JakKernelInst.inst_crude
-- auditor: targets 1a, 1b applied directly at concrete nondegenerate data (H2 = diag(x 0), N = 216)
example (x : Idx 3 3 2) := RBM.Univ.im_Gres_apply_self RBM.Univ.JakKernelInst.H2_herm (1/3) (by norm_num : (0:ℝ) < 1/2) x
example (x : Idx 3 3 2) := RBM.Univ.sum_mass_window_le_im_green RBM.Univ.JakKernelInst.H2_herm (by norm_num : (0:ℝ) < 1/4) (by norm_num : (0:ℝ) ≤ 1) (1/2) x
$ grep -c "^def T2267\|^noncomputable abbrev T2267" scratch2.lean
13
$ lake env lean scratch2.lean ; echo exit $?
exit 0
```
Vocabulary (check 2.1) against the library:
```
$ diff <(grep -A2 '^def jakGridGood' check | sed 's/{n : Type\*} \[Fintype n\] \[DecidableEq n\] //') <(grep -A2 '^def jakGridGood' JakKernel.lean)
(empty) -> jakGridGood body identical; binders come from `section Generic` `variable {n : Type*} [Fintype n] [DecidableEq n]` (:43)
```
I also read the statements in the file (`:48`, `:93`, `:147`, `:854`, `:933`). Hypothesis order, implicit/explicit binders, `lam` after `hL`, `N = ((W * L) ^ d : ℕ)` and the constants in `hα₁`, `hα₂`, `hQb` all match check 2.2–2.3 token for token. The only differences are `Type*` instead of `Type`, the section binders, and added hypothesis names. No `3 ≤ d` is assumed, and `3 ≤ L` is the only lattice hypothesis, as §29 (3) requires.

| target | statement | verdict |
|---|---|---|
| 1a `im_Gres_apply_self` | = pin (0 < η; RBM2D had η ≠ 0, which the ticket changes on purpose) | PASS |
| 1b `sum_mass_window_le_im_green` | = pin | PASS |
| 1c `sum_mass_window_le_of_im_green_le` | = pin | PASS |
| `jakGridGood` (vocabulary) | = check 2.1 | PASS |
| 2a `jak_pointwise_good` | = pin | PASS |
| 2b `jak_pointwise_crude` | = pin | PASS |
| 3 instances (6 + `H1`, `y0`) | = check 2.4 | PASS |

## 4. Hidden hypotheses, vacuity, cycles

- No `structure` or `class` is declared in the file. Every hypothesis is visible in the signatures. `jakGridGood` is a plain `def` with an explicit `∀ j x, Im ≤ Cb` body and contains no pin.
- No pin (`UNJak`, `UNUyw`, `UNJakUywRow`, `UNJakk`, …) appears in any statement. No external hypothesis is introduced, so no limit check is needed.
- There is no cycle: the file imports only the merged `JakSpectral` and Mathlib, and every dependency is on main.
- Non-vacuity:
  - `inst_good` discharges every hypothesis of 2a at `d=3, L=3, W=2` (`N = 216`), with `H = 1`, `u = w 0 = I`, `ηt = Cb = w' = 1` and `K = K' = 1`.
  - The grid events are discharged by `gridGood_one` (a theorem, not an assumption). The window bound is discharged by `blockM_le_432` (from the merged `sum_norm_blockM_le`). The constants `α₁ = 3079404`, `α₂ = 186624` and `Qb = 29/2` are discharged by `norm_num`.
  - `Bad ≡ False` here. The extra unpinned `example` (`:1058`) uses the non-scalar `H2 = diag(x 0)` with `Bad a ↔ a = 0`, so the `α₂` branch is also reachable.
- Private helpers: the count of `private` declarations whose names do not start with `JakKernel_` is `0`. The public names are the pinned ones plus `JakKernelInst.H1_herm`, `H2` and `H2_herm`, all in the instance namespace.
- Name-clash grep on main (`grep -rnw <name> RBM3D/ RBM3D.lean`, excluding the new file) gives 0 hits each for: `im_Gres_apply_self`, `sum_mass_window_le_im_green`, `sum_mass_window_le_of_im_green_le`, `jakGridGood`, `jak_pointwise_good`, `jak_pointwise_crude` and `JakKernelInst`.

## 5. Compiled nonempty instances (per endpoint theorem)

| target | instance in the file | data |
|---|---|---|
| 1a | used by `JakKernelInst.im_Gres_le_inv`, which `gridGood_one H1_herm` applies at `H1`, `η = 1` | `N = 216` |
| 1b | applied inside the proof of 1c (`:153`), hence at `H1`, `η = r = 1` through `inst_window` | `N = 216` |
| 1c | `inst_window` (`H1`, `η = r = Cb = 1`, `E₀ = 0`, `x = y0`) | nondegenerate |
| 2a | `inst_good` (all `y`, `σ₁`, `σ₂`) and the `H2` example | nondegenerate |
| 2b | `inst_crude` (`H1`, `s = {0}`, `u = w 0 = I`, `y0`) | nondegenerate |

All instances compile (§2) and every deterministic hypothesis is discharged. None uses `N = 0`, an empty index, a collapsed window or a `False` premise.

## 6. Paper deltas

The file is a deterministic port and states no paper statement. The ticket expects no new paper delta. The prove report's (d) has T2267a (a design-table row and the UN-22 hint, no paper statement) and says there is no T2267b. 1a's `0 < η` (RBM2D: `η ≠ 0`) is a difference from RBM2D, not from this paper; it is the ticket's pinned form. Coverage is complete.

## 7. Observations (no verdict effect)

- O1. Targets 1a and 1b have no instance of their own among the pinned `JakKernelInst` theorems. Inside the file they are applied at concrete data only through `im_Gres_le_inv`/`gridGood_one` and through the proof of 1c. The ticket pins the instance set this way. The auditor's scratch check (§3, last two `example`s) applies both directly at `H2`, `N = 216`, and compiles. The hub may want a direct `example` in a later touch, but this is not required here.
- O2. Registry pre-check: the audit worktree's cache has no root `RBM3D.olean`, so I did not rerun it. The prove report (`:226-234`) pastes it with exit 0 and an unchanged owed count. `Axioms.lean` is untouched (§1). The hub's full `lake build` at merge runs `#assert_rbm_axioms`.
- O3. The branch base is 8bb6f82, and main has since moved to 061aa73 (T2266/T2260/T2255 merges, all in other files). The three-dot diff touches only `JakKernel.lean`.

## Verdict

**PASS**: all targets (1a, 1b, 1c, `jakGridGood`, 2a, 2b and the instances in 3). No dispatcher sign-off is needed.
