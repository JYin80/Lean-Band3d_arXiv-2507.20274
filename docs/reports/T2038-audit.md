Auditor model: claude-opus-5-5

# T2038 audit (round 1) — S1-11 `Green/RowIndep` — Sat Oct  3 06:27:35 UTC 2026 (`date -u`)
Branch `t/T2038` @ `9d784bf`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2038-audit1` (detached). Main @ `6231342`, merge base `55f30d1`.
Target: `RBM.Green.highProb_norm_rowSum_sq_le` (key statement, RBM2D `Green/RowIndep.lean:1330` @ `c9a24cf`) plus every other public declaration of the port (ST1-COMMON item 6).

## 1. Scope
```
$ git diff --stat main...t/T2038
 RBM3D/Green/RowIndep.lean | 1595 +++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean    |    3 +-
$ git diff main...t/T2038 -- RBM3D/Test/Axioms.lean   (only change)
-   `RBM.Green.Stable]         -- stability of `1 − ξS` with constant `K`; band profile S1-24
+   `RBM.Green.Stable,         -- stability of `1 − ξS` with constant `K`; band profile S1-24
+   `RBM.Green.AgreeOffRow]    -- two samples agree on every coordinate off row `i` (S1-11 RowIndep)
$ grep -n "^import" RBM3D/Green/RowIndep.lean | grep RBM3D
11:import RBM3D.Gauss.DominationAt
12:import RBM3D.Gauss.FineModel
13:import RBM3D.Gauss.LinearForm
14:import RBM3D.Green.EntryCore
```
Only the two sole writable files; registry edit is an append in `structuralProps`; imports are merged MD/ST-1 files, no `RBM3D` root, no ST-2…6 file.

## 2. Statement (independent script diff against RBM2D `c9a24cf`, renaming R1–R4 by regex)
Script `stmtdiff.py` (scratchpad): extracts every declaration header up to `:=` from RBM2D lines 56–1418 and RBM3D lines 81–1451, applies R1 (`d : Sizes`→`sz : Sizes d`, `d.X`→`sz.X`), R2 (`Idx (`→`Idx d (`, `Xentry`/`idxKey` gain `d`), R4 (`svar (L) (W)`→`svarF d (L) (W) (sz.lam n)`, `gvar`→`gvarF d`), `seqHflow/slice/seqGvar d`→`… sz`, and compares; for `def`/`abbrev` it compares the full body.
```
$ python3 stmtdiff.py r2d.lean RBM3D/Green/RowIndep.lean
public RBM2D 66 public RBM3D 66
only RBM2D: []  only RBM3D: []
public statements differing after renaming: 0
defs/abbrevs RBM2D 17 RBM3D 17
DEFDIFF rowCoord   (2D `idxKey (sz.L n) (sz.W n)` vs 3D `idxKey d (sz.L n) (sz.W n)`: R2 only)
DEFDIFF rowSign    (same `idxKey d` renaming only)
```
(The header regex counts 66 public declarations; the prover's count 68 includes multi-keyword forms; either way no public name is only on one side.) Every public statement and every definition body equals RBM2D's after the renaming rules; the one semantic change is `svar` → `svarF … (sz.lam n)` in `rowVarSum`/`linVar_row*`/`integral_norm_row_sum_pow_le`, which is R4.

Key target as compiled (`RowIndep.lean:1360`):
```
theorem highProb_norm_rowSum_sq_le (hu : 0 ≤ u)
    (hsize : Filter.Tendsto sz.size Filter.atTop Filter.atTop)
    {U : ℕ → Type*} [∀ n, Fintype (U n)] {Ccard : ℝ}
    (hcard : ∀ᶠ n : ℕ in Filter.atTop, (Fintype.card (U n) : ℝ) ≤ (sz.size n : ℝ) ^ Ccard)
    (row : ∀ n, U n → Idx d (sz.L n) (sz.W n))
    (C : ∀ n, U n → Sizes.SeqΩ sz → Idx d (sz.L n) (sz.W n) → ℂ)
    (hCmeas : ∀ n q, Measurable (C n q))
    (hC : ∀ n q (ω ω' : Sizes.SeqΩ sz),
      (∀ c ∈ offRowCoord sz n (row n q), ω c = ω' c) → C n q ω = C n q ω')
    {τ : ℝ} (hτ : 0 < τ) :
    HighProbAt (Sizes.seqP sz) sz.size (fun n => {ω | ∀ q : U n,
      ‖rowSum sz n u (row n q) (C n q) ω‖ ^ 2
        ≤ (sz.size n : ℝ) ^ (2 * τ) * rowVarSum sz n u (row n q) (C n q) ω}) :=
$ grep -n "def HighProbAt" -A1 RBM3D/Defs/StochDomAt.lean
82:def HighProbAt (P : Measure Ω) (size : ℕ → ℕ) (Ξ : ℕ → Set Ω) : Prop :=
83-  ∀ D > (0 : ℝ), ∀ᶠ l : ℕ in atTop, P (Ξ l)ᶜ ≤ ENNReal.ofReal ((size l : ℝ) ^ (-D))
```
Mathematics: `|∑_{k≠i} H_{ik} C_k|² ≤ N^{2τ} u ∑_{k≠i} S_{ik}|C_k|²` simultaneously over `q ∈ U n`, `#U n ≤ N^{Ccard}`, with probability `≥ 1 − N^{-D}` eventually, every `τ, D > 0`; `C` measurable and determined by off-row coordinates (the independence premise of the LDE). Quantifier order: fixed `τ`, `U`, `Ccard`, then `∀ D, ∀ᶠ n` — the standard `≺` form. Scale `N = sz.size n = (W L)^d`; no exponent changed from RBM2D (`N^{2τ}`, `N^{Ccard}`, `N^{-D}`). Matches the ticket's mathematics (row LDE input of `lem_GbEXP`, paper `3_5_Loop_Hierarchy.tex:37` cites it as standard). **PASS**.

`d = 2` tokens (ticket bullet 1; portmap row 59):
```
$ git -C ../RBM2D show c9a24cf:RBM2D/Green/RowIndep.lean | grep -nE "Z2|zdist2|\(1 : ℝ\) / 5"
1135:    simp [Idx, Z2, Sizes.size, ZMod.card, sq]         -> replaced by Sizes.card_Idx (R2/R3)
1422:Two checks ... (`Idx 3 1 = Z2 3`):                   -> private Checks docstring, not ported
1586:      = if k ∈ ({(0, 0), ...}) then (1 : ℝ) / 5     -> private Checks section, not ported
$ grep -cE "zdist2" r2d.lean
0
```
`1/5` is the `d = 2` five-point weight of RBM2D's `svar` (`Model.lean:44`, `(5:ℝ)⁻¹ * W⁻²`), only in the private `Checks` section; not an exponent and not in any public statement; for `d ≥ 3` the profile is `svarF` (R4). Accounted for; no change beyond the renaming rules.

## 3. Vacuity, hidden hypotheses, cycles
- No structure-valued hypothesis; the target's hypotheses are exactly `hu, hsize, hcard, hCmeas, hC, hτ` (RBM2D's). `hC` (off-row measurability) and `hsize` are genuine conditions, discharged at the instance below.
- `AgreeOffRow` (a `Prop` on two samples, `RowIndep.lean:304`) is a plain definition taken as hypothesis by two congruence lemmas; registered as structural (DECISIONS §20).
- Dependencies are merged files only (imports above; `stochDomAt_of_momentDomAt` in merged `Gauss/DominationAt`); no import of anything downstream; no cycle.
- No external hypothesis (no `[YY_25]`-type pin), so no limit check needed.

## 4. Compiled nonempty instance
```
$ sed -n 1483,1493p RBM3D/Green/RowIndep.lean
theorem highProb_norm_rowSum_sq_le_sz0 (z : ℂ) :
    HighProbAt (Sizes.seqP sz0) sz0.size (fun n => {ω | ∀ q : LdeIdx sz0 n,
      ‖rowSum sz0 n 1 q.1 (minorCol sz0 n 1 z q.1 q.2) ω‖ ^ 2
        ≤ (sz0.size n : ℝ) ^ (2 * (1 / 10 : ℝ)) *
          rowVarSum sz0 n 1 q.1 (minorCol sz0 n 1 z q.1 q.2) ω}) :=
  highProb_norm_rowSum_sq_le (U := fun n => LdeIdx sz0 n) (Ccard := 2) zero_le_one
    sz0_size_tendsto (eventually_card_LdeIdx_le sz0) (fun _ q => q.1)
    (fun n q => minorCol sz0 n 1 z q.1 q.2) (fun _ q => measurable_minorCol 1 z q.1 q.2)
    (fun _ q _ _ h => minorCol_congr 1 z q.2 h) (by norm_num)
$ grep -n "^theorem LdeIdx_nonempty_sz0\|^theorem .*_sz0" RBM3D/Green/RowIndep.lean
1473:theorem LdeIdx_nonempty_sz0 (n : ℕ) : Nonempty (LdeIdx sz0 n) := by
1483:theorem highProb_norm_rowSum_sq_le_sz0 (z : ℂ) :
1495:theorem stochDom_rowSum_general_sz0 (z : ℂ) :
1507:theorem stochDom_rowSum_generalTime_sz0 (z : ℂ) :
1539:theorem integral_norm_row_sum_pow_le_sz0 :
1587:theorem exists_agreeOffRow_ne_sz0 :
```
Data: the MD-1 sequence `sz0` (`d = 3`, `L = 4(n+1)`, `W = (2(n+1))^5`; ST1-COMMON item 7), `u = 1`, `τ = 1/10`, `Ccard = 2`, `U n = LdeIdx sz0 n` (all (row, column) pairs, nonempty for every `n` by `LdeIdx_nonempty_sz0`), `C` = the minor-resolvent columns (the `lem_GbEXP` application), arbitrary `z`. Every hypothesis is discharged by a proof term; no `False` premise, no empty index, no hypothesis left open. Compiles (§5). **PASS**.

## 5. Build, axioms, hygiene (audit worktree)
```
$ lake build RBM3D.Green.RowIndep
Build completed successfully (3253 jobs).
exit=0                       (grep -ciE "warning|error" on the output: 0)
$ lake build | grep -E "error|Build" | tail -1
Build completed successfully (3735 jobs).        (warnings only in pre-existing files Path/Markov, Path/Stop, Propagator/PropUnit)
$ lake env lean ax2038.lean   # one #print axioms per top-level non-private theorem/def/abbrev, generated by awk
#print lines: 72   exit=0
70 x depends on axioms: [propext, Classical.choice, Quot.sound]
 2 x does not depend on any axioms
other lines: 0
'RBM.Green.highProb_norm_rowSum_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.RowIndepInst.highProb_norm_rowSum_sq_le_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "\b(sorry|admit|native_decide)\b|^\s*axiom\b|set_option" RBM3D/Green/RowIndep.lean
79:set_option linter.style.longLine false
$ cat pre2038.lean; lake env lean pre2038.lean   # registry pre-check (ST1-COMMON item 8)
import RBM3D
import RBM3D.Green.RowIndep
#assert_rbm_axioms
precheck_exit=0
axiom audit: 1255 theorems, 440 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: ...
```
No frozen signature touched (the only pre-existing file changed is `Test/Axioms.lean`, registry list only). **PASS**.

## 6. Paper deltas
Lean/paper differences: (i) the row LDE is stated as `HighProbAt` at scale `N = (WL)^d` along `sz` with explicit `Tendsto sz.size atTop atTop` and `#U ≤ N^{Ccard}` (paper has no such lemma, cites `[YY_25]`) — proposed `T2038a`; (ii) `rowVarSum` uses `svarF … (sz.lam n)` (merged FineModel profile carrying `g`) — proposed `T2038b` (recorded, no residual difference). Both proposed in the prove report (d). Covered.

## 7. Observations (no RETURN)
- O1. `git merge-tree --write-tree main t/T2038` reports `CONFLICT (content): Merge conflict in RBM3D/Test/Axioms.lean`: main (`1678ea4`, T2034) appended `` `RBM.EKFastDecay] `` at the same list end. Per DECISIONS §20 (3) the hub must take the union (keep both `EKFastDecay` and `AgreeOffRow`), not copy the branch file wholesale, then run the full build.
- O2. Prove report (b.5) counts 74 public axiom lines; this audit's generator found 72 (abbrev/sigma forms); both all-standard. No effect.
- O3. `set_option linter.style.longLine false` (file-level) mirrors existing merged practice; no warning in the module build.

## Verdict
`highProb_norm_rowSum_sq_le` and the other ported public declarations: **PASS**. No dispatcher sign-off needed (hub: union-merge `Test/Axioms.lean`, O1).
