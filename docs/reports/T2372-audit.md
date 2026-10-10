Auditor model: claude-opus-5-5

# T2372 audit (round 1): UN-10a `unNormBandRow`, Universality/NormBand.lean

Audit worktree `RBM3D-wt/T2372-audit1`, detached at `t/T2372` = 7df528d (merge base with `main`: f184210; `main` now c0a7747).
Scratch files in `scratchpad/T2372/`. Report written Sat Oct 10 07:04 UTC 2026 (`date -u`).

## 1. Diff scope
```
$ git diff --stat main...t/T2372
 RBM3D/Test/Axioms.lean           |   1 -
 RBM3D/Universality/NormBand.lean | 299 +++++++++++++++++++++++++++++++++++++++
 2 files changed, 299 insertions(+), 1 deletion(-)
$ git diff main...t/T2372 -- RBM3D/Test/Axioms.lean | grep '^[-+] '
-   `RBM.Univ.UNNormBandRow, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
```
Exactly the two sole writable files; registry: exactly the one `owedProps` line, `UNNormBound` stays. `Pins.lean` (the pin) is untouched.
Stop line: `wc -l NormBand.lean` = 299 ≤ 500.

## 2. Statement (target 1)
```
$ grep -n "^theorem\|^private theorem\|^def\|^example" RBM3D/Universality/NormBand.lean
66:private theorem NormBand_eig_le ...      91:private theorem NormBand_Xentry_le ...
105:private theorem NormBand_tail_arith ... 122:private theorem NormBand_tail_eventually ...
138:private theorem NormBand_gvar_le ...    155:private theorem NormBand_subgaussian ...
173:theorem unNormBandRow : UNNormBandRow := by
231:def H2 ...  233:theorem H2_isHermitian ...  237:theorem H2_entry_le ...  268:theorem Nsz_sz0_zero ...
272:theorem exp_ge ...  257/281/292/295: example
```
The target's type is the pin name itself, so no restatement can drift. Pin as elaborated (audit scratch `audit.lean`):
```
def RBM.Univ.UNNormBandRow : Prop :=
∀ (d : ℕ), 3 ≤ d → ∀ (𝔠 𝔡 : ℝ) (sz : Sizes d), sz.Admissible 𝔠 𝔡 → ∃ CV₀, 0 ≤ CV₀ ∧ UNNormBound sz (UNModel.band sz) CV₀
$ sed -n 477,479p RBM3D/Universality/Pins.lean
def UNNormBound (sz : Sizes d) (M : UNModel sz) (CV₀ : ℝ) : Prop :=
  ∀ D : ℝ, 0 < D → ∀ᶠ n in atTop,
    M.μ {ω | ∃ i, Nsz sz n ^ CV₀ < |(M.herm n ω).eigenvalues i|} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))
$ sed -n 116,121p RBM3D/Universality/Pins.lean
def UNModel.band {d : ℕ} (sz : Sizes d) : UNModel sz where
  μ := Sizes.seqP sz
  prob := inferInstance
  H := Sizes.seqXmat sz
  herm := Sizes.seqXmat_isHermitian sz
  meas := fun n i j => (measurable_Xentry d (sz.L n) (sz.W n) i j).comp (measurable_slice sz n)
```
Against the ticket's mathematics: "with probability ≥ 1 − N^{-D} every eigenvalue of `seqXmat` has |λ_i| ≤ N^{CV₀}",
quantifier order `∃ CV₀` before `∀ D > 0`, `∀ᶠ n` (fixed parameters before the limit), the band law `seqP`, the full
eigenvalue family, `N = Nsz sz n`. The proof fixes `CV₀ = 3` (line 175: `refine ⟨3, by norm_num, fun D hD => ?_⟩`),
uniform over `d, 𝔠, 𝔡, sz`; this is the general row, not a special case. **PASS.**

## 3. Hidden hypotheses, vacuity, cycles
- `unNormBandRow` has no hypotheses beyond the pin's binders; `UNModel.band`'s fields are concrete merged
  definitions (above), no `Prop` field carries an assumption.
- Route dependencies, all merged: `Sizes.seqP_map_eval`, `seqXmat_isHermitian`, `sum_sbKernelR`, `sbKernelR_nonneg`,
  `svarF_nonneg`, `Sizes.card_Idx`, `sz.three_le_L`, `sz.W_pos`, and `SizeTendsto` (`hA.2.2.1`) of `Admissible`.
  No pin is assumed; no external input (no new DECISIONS authorization needed).
- No cycle: `NormBand.lean` imports `Universality.Pins`, `Gauss.FineModel` and Mathlib only; nothing on the branch imports it.
- Math check of the route (read in the file): coordinate variance `gvarF ≤ 1` (diag `svarF = W^{-d}·sbKernelR ≤ 1`,
  off-diag `svarF/2`), proxy-1 sub-Gaussian, two-sided tail `2e^{-N²/2}` at threshold `N`, union over
  `#(Idx×Idx×Bool) = 2N²` coordinates, `4N²e^{-N²/2} ≤ N^{-D}` eventually from `N → ∞`; entries `≤ 2N`, ℓ^∞ bound
  `|λ_i| ≤ #Idx · 2N = 2N² ≤ N³` for `N ≥ 2`; `measure_mono` (no eigenvalue measurability). Consistent. **PASS.**

## 4. Compiled nonempty instances
```
$ sed -n 257p;264p;281p;292,295p RBM3D/Universality/NormBand.lean   (abridged to the statements)
example : H2 0 1 ≠ 0 ∧ ∀ i : Fin 2, |H2_isHermitian.eigenvalues i| ≤ 3 := by
  have h := NormBand_eig_le H2_isHermitian H2_entry_le i
example : 4 * Nsz sz0 0 ^ 2 * Real.exp (-(Nsz sz0 0 ^ 2 / 2)) ≤ Nsz sz0 0 ^ (-(1 : ℝ)) := by
example : ∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz0 (UNModel.band sz0) CV₀ :=
  unNormBandRow 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible
example : UNNormBandRow := unNormBandRow
```
- Endpoint: `unNormBandRow` applied at `d = 3`, `sz0`, `(𝔠,𝔡) = (1/6,1/10)` with every hypothesis discharged
  (`le_rfl`, merged `sz0_admissible`); `Nsz sz0 0 = 2097152` (`Nsz_sz0_zero`), nonempty index, not astronomically large.
- Deterministic step at a nondiagonal Hermitian `Fin 2` matrix (`H2 0 1 ≠ 0` proved in the example; `B = 3/2`).
- Threshold arithmetic at `sz0, n = 0, N = 2097152, D = 1`, both hypotheses of `NormBand_tail_arith` discharged
  (`exp_ge : 131073^8 ≤ e^{1048576}` via `1 + x ≤ e^x`).
Independent re-elaboration in the audit worktree:
```
$ cat audit.lean
import RBM3D.Universality.NormBand
open RBM RBM.Gauss RBM.Univ
#print axioms RBM.Univ.unNormBandRow
example : RBM.Univ.UNNormBandRow := RBM.Univ.unNormBandRow
#check (RBM.Univ.unNormBandRow 3 le_rfl (1/6) (1/10) RBM.Gauss.SizesInst.sz0 RBM.Gauss.SizesInst.sz0_admissible)
#print RBM.Univ.UNNormBandRow
$ lake env lean audit.lean; echo "exit=$?"
'RBM.Univ.unNormBandRow' depends on axioms: [propext, Classical.choice, Quot.sound]
unNormBandRow 3 le_rfl (1 / 6) (1 / 10) SizesInst.sz0
  SizesInst.sz0_admissible : ∃ CV₀, 0 ≤ CV₀ ∧ UNNormBound SizesInst.sz0 (UNModel.band SizesInst.sz0) CV₀
def RBM.Univ.UNNormBandRow : Prop := (as in §2)
exit=0
```
**PASS.**

## 5. Build, axioms, hygiene
```
Sat Oct 10 05:52:22 UTC 2026
$ lake build RBM3D.Universality.NormBand 2>&1 | grep -E "error|NormBand|Build completed|sorry" | tail -8
✔ [3333/3333] Built RBM3D.Universality.NormBand (3.7s)
Build completed successfully (3333 jobs).
exit=0
$ lake env lean docs/tickets/checks/T2372-check.lean >/dev/null 2>chk.err; echo "check exit=$?"; grep -c error chk.err
check exit=0
0
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Universality/NormBand.lean
(no output)
```
Axioms of the target: `[propext, Classical.choice, Quot.sound]` (§4). Frozen signatures: none touched (`Pins.lean`
not in the diff). Name clash: `git grep unNormBandRow main` finds only a docstring mention in `Main/BUnivHolds.lean:26`
(prove report (b)); no declaration clash.

Registry pre-check (`import RBM3D` + `import RBM3D.Universality.NormBand` + `#assert_rbm_axioms`): the auditor's
own run did not finish. `lake build RBM3D` in the audit worktree recompiled unrelated certificate modules
(`Graph/LWExpCertBS0.lean` still compiling after 1:00:54, `Graph/LWExpCertS1.lean` after 33:47, `ps -eo etime`),
and the auditor stopped it at 07:04 UTC; the queued `lake env lean precheck.lean` then printed
`precheck exit=1` / `error: object file '.../.lake` (root olean missing because the build was stopped, not a registry error). Evidence on file: the prove report (b) pastes the pre-check with `exit=0`,
`grep -c UNNormBandRow precheck.out` = 0, and a simulated merge `lake build` with `exit=0`. The theorem
`unNormBandRow : UNNormBandRow` now proves the deleted owed premise. The hub's full `lake build` at merge
(rule (A)5) runs `#assert_rbm_axioms` and is the binding check.

## 6. Paper deltas
- No new Lean/paper statement difference: the target is the merged pin `UNNormBandRow`, unchanged.
- Candidate `T2372a` (prove report (d)) is a doc fix. The pin docstrings (`Pins.lean:470-475`, `:830-833`) claim
  `CV₀ = 1` from `|h_xy| ≤ 1` w.h.p., which is false for variance-1 Gaussians (`P(|g|>1/2) = 0.617`, pasted).
  The proof uses `CV₀ = 3`. The pin's statement (`∃ CV₀ ≥ 0`) is unaffected. Coverage complete.

## Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1. The public instance helpers `RBM.Univ.NormBandInst.{H2, H2_isHermitian, H2_entry_le, Nsz_sz0_zero, exp_ge}`
  are neither `private` nor stem-prefixed by name. The stem appears only as the namespace `NormBandInst`.
  This is borderline under §3 (E). No name clash was found.
- O2. `main` (c0a7747, T2371 merged) still has the line at `Test/Axioms.lean:196`
  (`git show main:RBM3D/Test/Axioms.lean | grep -n UNNormBandRow` → `196:` and `183:` comment). Under H23 (b)
  the hub re-applies this one-line deletion against current `main`. The `:183` comment (T2371's) still calls
  `UNNormBandRow` "owed (producer T2372)"; that wording is for the dispatcher to update.
- O3. `bUniv_holds` (`Main/BUnivHolds.lean:228`) still takes `UNNormBandRow` as a hypothesis. Discharging it with
  `unNormBandRow` is a consumer edit outside this ticket's files.

## Verdict
- Target 1 `unNormBandRow`: **PASS**
- Target 2 instances: **PASS**
- Target 3 registry line: **PASS** (one line; the auditor's pre-check did not complete; the hub's merge build is binding)

T2372: PASS. No dispatcher sign-off needed.
