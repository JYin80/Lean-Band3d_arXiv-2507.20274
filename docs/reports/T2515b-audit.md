Auditor model: claude-opus-5-5
# T2515b audit, round 3 (row b: `BA/GUEEntry`, `BA/GUEEntry2`; targets 9-13), Fri Oct 16 10:07:34 UTC 2026
Scope: Amend 1 item 5 (i)-(iv) only (CONTROL H321, DECISIONS §347). Detached worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2515b-audit3r` at `t/T2515b`. Scratch scripts in the session scratchpad `T2515b/`.

## (i) Head of `t/T2515b`
```
$ git rev-parse t/T2515b
f158d5f5b8a947b596fc18483b710526438475e7
$ git log --oneline -3 t/T2515b
f158d5f5 T2515b repair: compiled obstruction to a fully discharged X = 0 instance of mixEntry_detBA / mix_detBA at 0 < a + b
f8250a35 T2515b: BA GUEEntry section 3 (full build: bundle GUEEntry_Setup and its users private)
0435297e T2515b: BA GUEEntry section 2 (target 13: compiled instances in GUEEntry2.lean)
$ git diff --stat main...HEAD
 RBM3D.lean              |    2 +
 RBM3D/BA/GUEEntry.lean  | 1524 +++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/BA/GUEEntry2.lean | 1570 +++++++++++++++++++++++++++++++++++++++++++++++
 3 files changed, 3096 insertions(+)
```
Head = `f158d5f5`, the commit audited in round 2: no Lean change since round 2. Diff touches only the sole writable files
(`GUEEntry`, `GUEEntry2`) and the two `RBM3D.lean` import lines (as round 2 §1).

## (ii) Statements of targets 9-12 unchanged
Script `ext.sh <rev>`: for each target, print from the `theorem|def <name>` line to the first line containing `:=`.
```
$ grep -nE '^(theorem|def) (stable_mixBA|mix_detBA|mixEntry_detBA|mixMatBA|GUEEntry_mixMatBA_eq_Xmat|
    GUEEntry_mixMatBA_isHermitian|GUEEntry_ouMatC_ba_eq_mixMatBA|GUEEntryMixBA|gueEntryMixBA)\b' (cut)
RBM3D/BA/GUEEntry.lean:68:theorem stable_mixBA ...       RBM3D/BA/GUEEntry.lean:1376:theorem mix_detBA ...
RBM3D/BA/GUEEntry2.lean:85:theorem mixEntry_detBA ...    RBM3D/BA/GUEEntry2.lean:448:def mixMatBA ...
RBM3D/BA/GUEEntry2.lean:453:theorem GUEEntry_mixMatBA_eq_Xmat ...  :459 GUEEntry_mixMatBA_isHermitian  :468 GUEEntry_ouMatC_ba_eq_mixMatBA
RBM3D/BA/GUEEntry2.lean:738:def GUEEntryMixBA (d : ℕ) : Prop :=    :785 theorem gueEntryMixBA (hd : 3 ≤ d) : GUEEntryMixBA d := by
$ for r in f8250a35 f158d5f5; do bash ext.sh $r > stmt_$r.txt; done; diff stmt_f8250a35.txt stmt_f158d5f5.txt && echo IDENTICAL
IDENTICAL
$ shasum stmt_*.txt
54a42379b735c727d415dfd216e536765f53a1e1  stmt_f158d5f5.txt
54a42379b735c727d415dfd216e536765f53a1e1  stmt_f8250a35.txt
$ for r in f8250a35 f158d5f5; do git show $r:RBM3D/BA/GUEEntry2.lean | sed -n 738,784p | shasum; done   # pin body
d943bcc379ad275f1d4bfdd5a7d8ff6204028811  -
d943bcc379ad275f1d4bfdd5a7d8ff6204028811  -
$ git diff f8250a35 f158d5f5 | grep -E '^@@|^-[^-]'
@@ -1189,6 +1189,351 @@ example (ω : sz0.SeqΩ) (x y : Vtx 3 (sz0.L n₁) (sz0.W n₁)) :
```
The statements (and the full body of the pin `GUEEntryMixBA`, lines 738-784) are byte-identical to the round-1 text
`f8250a35` that round 2 §2 checked against the signed pin; the repair is a pure insertion after line 1189 (no `-` line).
Pin head as extracted (`GUEEntry2.lean:738-743`):
```
def GUEEntryMixBA (d : ℕ) : Prop :=
  ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
  ∀ (g E : ℕ → ℝ) (m : ℕ → ℂ), (∀ n, 0 < g n ∧ g n ≤ 𝔡⁻¹ ∧ BAReal d (sz.L n) (g n) κ (E n) (m n)) →
  ∀ n0 : ℕ, ∀ K : ℕ → ℕ, (∀ n, K n ≤ (sz.size n) ^ n0) → ∀ a b : ∀ n, Fin (K n + 1) → ℝ,
  (∀ n k, 0 ≤ a n k ∧ 0 ≤ b n k ∧ 0 < a n k + b n k ∧ a n k + b n k < 1) →
  ∀ (c₀ : ℝ) (δ : ℕ → ℝ), 0 < c₀ → (∀ n, 0 ≤ δ n) →
```
**(ii): OK.**

## (iii) Binders of the examples at `GUEEntry2.lean:1032`, `:1049`, and their compilation
Script `binders.py`: read the `example` header up to the line ending in `:=`/`:= by`, list the top-level binder groups.
```
$ python3 -I binders.py RBM3D/BA/GUEEntry2.lean 1032 1049
example at :1032 (9 header lines): 8 binder groups
   { X
   ( hX
   ( hllErr
   ( hrow
   ( hcol
   ( hquad
   ( hdiag
   ( i j
example at :1049 (14 header lines): 9 binder groups
   ( ω
   { Lm
   ( hΩ
   ( hLrow
   ( hLcol
   ( hLquad
   ( hLdiag
   ( hLm
   ( x y
$ grep -n 'abbrev n₁' RBM3D/BA/GUEEntry2.lean
1001:private abbrev n₁ : ℕ := 25
```
Against Amend 1 item 1:
| example | open in Lean (besides the entry indices of the conclusion) | Amend 1 item 1 list | match |
|---|---|---|---|
| `:1032` `mixEntry_detBA` | `X`, `hX`, `hllErr`, `hrow`, `hcol`, `hquad`, `hdiag` | `X` (`hX`), `hllErr`, `hrow`, `hcol`, `hquad`, `hdiag` | exact |
| `:1049` `mix_detBA` | `ω`, `Lm`, `hΩ`, `hLrow`, `hLcol`, `hLquad`, `hLdiag`, `hLm` | `ω` of `sz0` at `n = 25`, `hΩ`, `hLrow/col/quad/diag`, `hLm` (with `Lm`) | exact |
`i j` / `x y` are the universally quantified entry indices of the conclusion, not hypotheses. All other arguments of the two
applications are discharged in the file at the concrete data (`d = 3`, `sz0` at `n₁ = 25`, `(a, b) = (1/4, 1/4)`, `δ = 10⁻¹²`,
`Φ = 1`, `κ = 1/2`, `Λ = 1/64`) by `norm_num`, `sz0.three_le_L`, `le_rfl`, `GreenCore_carrier` (`:1049`: resolvent identities,
`M`, `D`, `z`) and the hypothesis-free private lemmas:
```
$ grep -nE '^private theorem GUEEntryInst_(g|real|dlt|wd|cs) ' RBM3D/BA/GUEEntry2.lean | cut -c1-120
987:private theorem GUEEntryInst_dlt : (1 : ℝ) / 10 ^ 12 ≤ GUEEntry_dlt 3 (1 / 64) (1 / 2) := by
993:private theorem GUEEntryInst_cs : GUEEntry_cs 3 (1 / 64) (1 / 2) * 1 * ((1 : ℝ) / 10 ^ 12) ^ 2 ≤ 1 := by
1006:private theorem GUEEntryInst_real : BAReal 3 (sz0.L n₁) g₁ (1 / 2) E₁ m₁ :=
1009:private theorem GUEEntryInst_g : 0 < g₁ ∧ g₁ ≤ 1 / 64 := by
1017:private theorem GUEEntryInst_wd : (((sz0.W n₁ : ℕ) : ℝ) ^ 3)⁻¹ ≤ ((1 : ℝ) / 10 ^ 12) ^ 2 := by
```
The Hermitian property `hH` and `Im z > 0` (`hzim`) of `:1049` are proved inside the example (lines 1063-1084).
Build (fresh: the `GUEEntry2.olean` timestamp is the build time, 03:06 local = 10:06 UTC):
```
$ lake build RBM3D.BA.GUEEntry RBM3D.BA.GUEEntry2 2>&1 | grep -E "error|warning: .*sorry|Build completed"
Fri Oct 16 10:05:46 UTC 2026
Build completed successfully (3808 jobs).
Fri Oct 16 10:06:55 UTC 2026
$ lake env lean RBM3D/BA/GUEEntry2.lean > e2.txt 2>&1; echo exit=$?; grep error e2.txt     (10:07:03 -> 10:07:24 UTC)
exit=0
$ grep -cE '\b(sorry|admit|native_decide)\b|^axiom ' RBM3D/BA/GUEEntry.lean RBM3D/BA/GUEEntry2.lean
RBM3D/BA/GUEEntry2.lean:0
RBM3D/BA/GUEEntry.lean:0
```
**(iii): OK** (open hypotheses exactly as ruled in Amend 1 item 1; both examples compile).

## (iv) Axioms
```
$ lake env lean ax.lean     # imports RBM3D.BA.GUEEntry, RBM3D.BA.GUEEntry2; #print axioms of each target
'RBM.BA.stable_mixBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.mix_detBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.mixMatBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.mixEntry_detBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GUEEntryMixBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.gueEntryMixBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GUEEntry_ouMatC_ba_eq_mixMatBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GUEEntry_mixMatBA_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GUEEntry_mixMatBA_eq_Xmat' depends on axioms: [propext, Classical.choice, Quot.sound]
```
**(iv): OK** (standard three for every target).

## Paper deltas
No change: candidates `T2515c`-`T2515e` of the prove report (d)5 as in round 2 §5; the `T2515d` addendum (the `hwd` + `hΦδ`
exclusion of the `X = 0` witness, `GUEEntry2:1420`, `:1485`) is recorded by the dispatcher at merge (Amend 1 item 4).

## Verdict per target (under Amend 1 item 1)
| target | (i) head | (ii) statement | (iii) instance | (iv) axioms | verdict |
|---|---|---|---|---|---|
| 9 `stable_mixBA` | OK | unchanged | `:926` (round 2) | OK | PASS |
| 10 `mix_detBA` | OK | unchanged | `:1049`, open set = Amend 1 list, compiles | OK | PASS |
| 11 `mixMatBA` + identities, `mixEntry_detBA` | OK | unchanged | `:1539-1563`; `:1032`, open set = Amend 1 list, compiles | OK | PASS |
| 12 `GUEEntryMixBA` / `gueEntryMixBA` | OK | unchanged (pin body hash) | `:961` (round 2) | OK | PASS |
| 13 instances | OK | — | per Amend 1 item 1 | — | PASS |
**Ticket verdict: PASS** on Amend 1 item 5 (i)-(iv). No dispatcher sign-off needed beyond Amend 1.

## Observations (no statement/instance/build/axiom/delta effect)
1. File sizes 1,524 / 1,570 (≤ 2,000 each), as Amend 1 item 3.
2. Round-2 observations 2-5 stand unchanged (not re-examined; out of round-3 scope).
