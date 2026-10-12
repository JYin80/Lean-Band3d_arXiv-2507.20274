Auditor model: claude-opus-5-5
# T2438 audit (round 1) — Mon Oct 12 04:54:43 UTC 2026

Branch `t/T2438` at `7c201be`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2438-audit1` (detached, built from scratch cache clone).
Targets: (1) `baTwistGridTail_holds (d : ℕ) : BATwistGridTail d`; (1b) public `TwistGridTail_condMGF_Z`; (2) instance; (3) registry: none.

## 1. Statement
The target's type is the merged pin itself; the pin file is untouched by the branch.
```
$ git diff main...t/T2438 -- RBM3D/BA/TwistGrid2.lean | wc -l
       0
$ sed -n '304p' RBM3D/BA/TwistGridTail2.lean
theorem baTwistGridTail_holds (d : ℕ) : BATwistGridTail d := by
$ lake env lean ax.lean   (contains `#check @RBM.BA.baTwistGridTail_holds` and `example : ∀ d, BATwistGridTail d := baTwistGridTail_holds`)
baTwistGridTail_holds : ∀ (d : ℕ), BATwistGridTail d
$ grep -nE "def BATwistGridTail" RBM3D/BA/TwistGridTail*.lean   (no shadowing redefinition)
(no output)
```
The pin, `TwistGrid2.lean:239-246` on main, has every `d`, no `3 ≤ d`, fixed parameters `κ ε 𝔡 𝔠 sz z`, `BAFlow`, window `0 ≤ s ≤ t ≤ T0`, `D > 0`, then `∃ CK ≥ 0`, then `∀ K` with `K n ≠ 0` and eventually `N^{CK} ≤ K n`, then `∀ ε' > 0`, `∀ᶠ n`, `∀ i`, and
`P(∃ k ≤ K n, N^{ε'}(Σ_{j<k} Δ‖twEEk_j‖ + N^{-D})^{1/2} < ‖twMart_k‖) ≤ N^{-D}`. This is clause (iii) of T2428 4 (b) as the ticket asks. The theorem is general, not a special case: `d` is arbitrary and the only instantiation is `CK := 2 * D + 20` (`TwistGridTail2.lean:306`), which depends on `D` alone.

**Target 1b, `TwistGridTail_condMGF_Z`** (`TwistGridTail.lean:949-972`). The ticket asks for general weights `κ` and the random proxy `Δ·Re Σ κ_b κ̄_{b'} twEEM(b,b')`. The statement has:
- hypotheses `Im m_F > 0`, `u_{j+1} < 1`, `Δ ≥ 0`, and arbitrary `κ : Zd d (sz.L n) → ℂ` and `r : ℝ`;
- conclusion: integrability of `exp(r·Re Z)` and `exp(r·Im Z)`, and `E[exp(r·Re Z) | filt j]` and `E[exp(r·Im Z) | filt j]` both `≤ᵐ exp(r²·(Δ·(Σ_b Σ_b' κ_b conj κ_b' twEEM_{u_{j+1}}(Hpath_j)(b,b')).re)/2)`.

Here `Z = stepZCN (sz.withLam 0) … (TwistGridTail_phi … u_{j+1} …) (fun _ a => κ a)`. This matches item 1 (b), and the lemma is public as required.

## 2. Vacuity, hidden hypotheses, cycles
- The target has no hypotheses beyond the pin's binders. There are no new structures or classes:
  ```
  $ grep -nE "^(theorem|def|lemma|abbrev|instance|structure)" RBM3D/BA/TwistGridTail*.lean | grep -v private
  RBM3D/BA/TwistGridTail2.lean:304:theorem baTwistGridTail_holds (d : ℕ) : BATwistGridTail d
  RBM3D/BA/TwistGridTail.lean:196:def TwistGridTail_phi (u : ℝ) (σ : Fin 2 → Bool)
  RBM3D/BA/TwistGridTail.lean:949:theorem TwistGridTail_condMGF_Z (j : ℕ) (σ : Fin
  $ grep -cE "^private" RBM3D/BA/TwistGridTail*.lean
  RBM3D/BA/TwistGridTail2.lean:3
  RBM3D/BA/TwistGridTail.lean:71
  ```
- `TwistGridTail_phi` is a plain definition, `twL2M … (g₀ Ψ + M)`, with no proof content.
- Imports are merged modules only. `TwistGridTail.lean:6-14` imports `BA.TwistGrid2`, `BA.EMn2BA`, `BA.GreenSchur`, `Path.DifREP2`, `Path.StepDecompLoop`, `Path.QVIdentity`, `Induction.StepDecompN`, `Induction.GridAssemblyN` and `Induction.AzumaProxyN2`. `TwistGridTail2` imports `TwistGridTail`. There is no cycle and no use of an unmerged pin.
- There is no external hypothesis, so no limit check is owed.

## 3. Compiled nonempty instances
The instances are in the same file, `TwistGridTail2.lean:413-447`, and compile (§4 build).
- **Example 1.** `baTwistGridTail_holds 3` at `(κ, ε, 𝔡, 𝔠) = (1/2, 1/10, 1/10, 1/6)`, `sz0`, `zSeq`, `flow_sz0`, `s ≡ 1/2`, `t ≡ 2/3`, `D = 1`, `K_n = ⌈N_n^{CK}⌉₊ + 1`, `ε' = 1/10`. Every hypothesis is discharged:
  - `0 ≤ 1/2` and `1/2 ≤ 2/3` by `norm_num`;
  - `t ≤ T0` by `t0_sz0`;
  - `K n ≠ 0` by `Nat.succ_ne_zero`;
  - `N^{CK} ≤ K n` for all `n` by `Nat.le_ceil`.
  `sz0` has `L_n = 4(n+1) ≥ 4` and `W_n = (2(n+1))^5`, so the index set is nonempty, and the window `1/2 < 2/3` is not collapsed.
- **Example 2.** `example : ∀ d, BATwistGridTail d := baTwistGridTail_holds`, the ticket's acceptance check.
- **Examples 3 and 4.** They feed `baTwistGridTail_holds 3` into `baTwistGridAssemble_holds 3 11`. `BATwistGridRem 3 11` (T2437) and `BATwistGridWTail 3` (T2439) stay hypotheses, which is allowed: they are other gates' pins.
- **condMGF instance** (`TwistGridTail.lean:1486-1497`). `TwistGridTail_condMGF_Z` is applied at `sz0`, `n = j = 0`, `K ≡ 4`, `κ = 1_{(1,0,0)}`, `r = 1`. Its hypotheses are discharged by `BAmF_sz0_im_pos 0` and `norm_num [gridTime, gridStep]`.

Verdict for instances: present and nondegenerate.

## 4. Build, axioms, hygiene, diff
```
$ lake build RBM3D.BA.TwistGridTail RBM3D.BA.TwistGridTail2 2>&1 | grep -E "^(error|warning): RBM3D/BA/TwistGridTail|Build completed|^error"; echo exit
Build completed successfully (4026 jobs).
exit=0
$ lake env lean ax.lean
'RBM.BA.baTwistGridTail_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.TwistGridTail_condMGF_Z' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.TwistGridTail_phi' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ lake env lean /Users/junyin/Lean_proof/RBM3D/docs/tickets/checks/T2438-check.lean >/dev/null 2>&1; echo "check exit=$?"   (on the branch)
check exit=0
$ grep -nE "sorry|admit|native_decide|^axiom|implemented_by|extern|unsafe|def BATwistGridTail|elab|macro" RBM3D/BA/TwistGridTail*.lean
(no output)
$ git diff --stat main...HEAD
 RBM3D/BA/TwistGridTail.lean  | 1501 ++++++++++++++++++++++++++++++++++++++++++
 RBM3D/BA/TwistGridTail2.lean |  449 +++++++++++++
 2 files changed, 1950 insertions(+)
$ git diff --name-only main...HEAD -- RBM3D.lean RBM3D/BA/TwistGrid2.lean RBM3D/BA/TwistGrid.lean | wc -l
       0
$ git grep -n "baTwistGridTail_holds\|TwistGridTail_condMGF_Z\|TwistGridTail_phi" main -- RBM3D | wc -l   (name clash on main)
       0
$ wc -l RBM3D/BA/TwistGridTail*.lean
    1501 RBM3D/BA/TwistGridTail.lean
     449 RBM3D/BA/TwistGridTail2.lean
```
- Both files are under the 2,000-line stop line.
- The diff touches only the sole writable files. No frozen signature changed. `RBM3D.lean` is untouched; the hub adds the import at merge.

## 5. Paper deltas
- The Lean statement is the merged pin, and no new statement difference is introduced.
- Azuma with a random predictable proxy in place of BDG is the existing delta D90 (`docs/paper-deltas.md:403`; also D479 `:1438`).
- The report proposes `T2438a`: the hard-coded `CK = 2D + 20` and QV constant `1` versus the band's `k`. Coverage is complete.

## 6. Observations (no statement, instance, build, axiom or delta effect)
- O1: The ticket says `TwistGridTail2` is used "only if the first file passes 1,700 lines". The prover split pre-emptively because the content total is 1,950 lines, so file 1 is 1,501 lines. `TwistGridTail2.lean` is a listed sole writable file, the import order is `TwistGridTail → TwistGridTail2` as named, and target 1 and its instance are in file 2 as the ticket's split prescribes.
- O2: Private band helpers are reached with `open private` (`TwistGridTail.lean:45-55`, `TwistGridTail2.lean:30-33`) instead of stem-prefixed copies (ticket 1a (iii)). This follows an existing pattern (`BA/Step2BA.lean:35`). A rename in `Path/DifREP2`, `Path/StepDecompLoop`, `Path/QVIdentity`, `Induction/StepDecompN` or `Induction/GridAssemblyN` would break the build but not change a statement. The prove report (d) records this.
- O3: The route uses `difRep2_peel` at `c = 1` and the `Y` moments from `stepDecompCN_Y_sq`, instead of `difRep2_peel_N` and `AzumaProxyN_YfieldsW`. These are internal route choices; the targets are unchanged.
- O4: Prove report (b) gives first `n = 8` for the budgets at the instance, while (a) gives 7, because of the looser `N⁹` shift constant. The theorem is eventual, and the example's conclusion is the eventual statement, so this does not affect the instance.

## Verdict
- Target 1 `baTwistGridTail_holds`: **PASS**
- Target 1b `TwistGridTail_condMGF_Z`: **PASS**
- Target 2 (instances): **PASS**
- Target 3 (registry: none): **PASS**
- Ticket T2438: **PASS**. No dispatcher sign-off needed.
