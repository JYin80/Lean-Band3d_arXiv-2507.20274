Auditor model: claude-opus-5-5

# T2078 audit (round 1) — S1-18 `Green/LDE.lean` (port of RBM2D `Green/FlucAvg`, `Green/LDE` at `c9a24cf`)

Date (`date -u`): Sat Oct  3 22:34:45 UTC 2026. Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2078-audit1`, detached at `t/T2078` = `df28c0e`; `main` = `3b98b27`. Scratch: `scratchpad/T2078/`.

## 1. Scope, hygiene, build

```
$ git diff --name-only main...HEAD
RBM3D/Green/LDE.lean
$ grep -nE '\bsorry\b|\badmit\b|native_decide|^\s*axiom ' RBM3D/Green/LDE.lean | wc -l
       0
$ grep -n "^import" RBM3D/Green/LDE.lean
6:import Mathlib.Analysis.Matrix.MeasurableSpace
7:import Mathlib.Topology.Instances.Matrix
8:import RBM3D.Green.EntryDom
9:import RBM3D.Green.FlucVanish
10:import RBM3D.Green.RowIndep
$ for f in EntryDom FlucVanish RowIndep; do git cat-file -e main:RBM3D/Green/$f.lean && echo "main has Green/$f.lean"; done
main has Green/EntryDom.lean
main has Green/FlucVanish.lean
main has Green/RowIndep.lean
$ lake build RBM3D.Green.LDE 2>&1 | grep -E "error|warning: declaration uses|Built RBM3D.Green.LDE|Build completed|failed"
✔ [3331/3331] Built RBM3D.Green.LDE (5.4s)
Build completed successfully (3331 jobs).
```
Only the sole writable file is touched (`RBM3D/Test/Axioms.lean` untouched, allowed). Imports are merged files only; no `RBM3D` root import, no ST-2+ import. No frozen signature is edited (new file).

## 2. Axioms (scratch `audit.lean`, `lake env lean`, exit 0)

```
'RBM.Green.eventually_le_W' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.stochDom_normSq_Hflow_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.stochDom_ldeRow' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.stochDom_ldeCol' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.LDEInst.eventually_le_W_sz0_million' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.LDEInst.stochDom_normSq_Hflow_diag_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.LDEInst.integral_norm_Hflow_diag_pow_szT' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.LDE_norm_flucAvg_le_of_boundedWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.Sblk2_diag_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.card_Sblk_support' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Registry pre-check (ST1-COMMON item 8), run by the auditor:
```
$ lake build RBM3D 2>&1 | grep -E "error|Build completed"
Build completed successfully (3819 jobs).
$ lake env lean precheck.lean   # import RBM3D; import RBM3D.Green.LDE; #assert_rbm_axioms
exit 0
1:axiom audit: 2607 theorems, 1076 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
99:premises found by scanning: 83 (borrowed 2, owed 67, structural 14).
$ diff precheck_base.out precheck.out   # base = without the LDE import
1c1
< axiom audit: 2540 theorems, 1073 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
---
> axiom audit: 2607 theorems, 1076 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
```
No new premise in the scan; no registry line needed.

## 3. Statements against the pin (RBM2D `c9a24cf` after ST1-COMMON R1-R4)

Script `sig2.py`: extracts every public signature of `FlucAvg.lean` (up to `### Checks`) and `LDE.lean` (up to `### Checks`) at `c9a24cf`, applies R1-R4 (`d : Sizes → sz : Sizes d`, `Idx (` → `Idx d (`, `Z2` → `Zd d`, `BlockIndex` → `Vtx d`, `Sblk2 (sz.L n) (sz.W n)` → `svar d … (sz.lam n)`, `svar` → `svarF d`, `spectralZ/M` → `zt/mE`, `PerTimeDomAt (Sizes.seqP sz) sz.size` → `sz.PrecPT`), and compares whitespace-free with the RBM3D file up to `namespace LDEInst`.
```
$ python3 sig2.py
RBM2D public 45 RBM3D public (before LDEInst) 46 identical after renaming 39
RBM3D-only: ['LDE_norm_flucAvg_le_of_boundedWeight']
-- card_blockAvg_support
  2D> … filter fun k => (blk (sz.L n) (sz.W n) k.1, blk (sz.L n) (sz.W n) k.2) = a).card = sz.W n ^ 2
  3D> … filter fun k => (split d (sz.L n) (sz.W n) k).1 = a).card = sz.W n ^ d
-- card_Sblk_support
  2D> … filter fun j => (blk … i.1, blk … i.2) - (blk … j.1, blk … j.2) ∈ sbSupport (sz.L n)).card = 5 * sz.W n ^ 2
  3D> … filter fun j => (split d … j).1 - (split d … i).1 ∈ flucVanish_sbSupport d (sz.L n)).card = (2 * d + 1) * sz.W n ^ d
-- rowVarSum_minorRowConj_eq
  2D> … = u * ldeColRHS (svarF d (sz.L n) (sz.W n)) (green …) k.1 j
  3D> … = u * ldeColRHS (svarF d (sz.L n) (sz.W n) (sz.lam n)) (green …) k.1 j
-- Sblk_diag_pos
  2D> theorem Sblk_diag_pos {L W : ℕ} [NeZero L] [NeZero W] (i : Vtx d L W) : 0 < Sblk2 L W i i
  3D> theorem Sblk_diag_pos {d L W : ℕ} (g : ℝ) [NeZero L] [NeZero W] (i : Vtx d L W) : 0 < svar d L W g i i
-- Sblk2_diag_eq
  2D> … Sblk2 L W i i = 1 / (5 * (W : ℝ) ^ 2)
  3D> theorem Sblk2_diag_eq {d L W : ℕ} (g : ℝ) … : svar d L W g i i = ((W : ℝ) ^ d)⁻¹ * (1 + 2 * (d : ℝ) * g ^ 2)⁻¹
-- integral_norm_Hflow_diag_pow
  2D> … = u ^ p * (RowIndep_dfac p * svarF d (sz.L n) (sz.W n) x x ^ p)
  3D> … = u ^ p * (RowIndep_dfac p * svarF d (sz.L n) (sz.W n) (sz.lam n) x x ^ p)
```
(output lines shortened with `…` only where both sides are identical.) Reading:
* `rowVarSum_minorRowConj_eq`, `integral_norm_Hflow_diag_pow`: only the extra `g = sz.lam n` argument of R4 `svarF` (my map omitted it); identical otherwise.
* `card_blockAvg_support`: `(blk k.1, blk k.2)` → `(split d L W k).1` is the R2 block map of `Zd d`; count `W^2 → W^d` (R3).
* `card_Sblk_support`, `Sblk_diag_pos`, `Sblk2_diag_eq`: genuine `d`-dimensional changes (constant `5 → 2d+1`, orientation `j − i`, profile `W^{-d}(1+2dg²)⁻¹` with `g`); the formula agrees with DECISIONS §30 ("同块取 `W^{-d}/(1+2dg²)`"). Covered by T2078a, T2078b (§5).
* Dropped: none. Added: `LDE_norm_flucAvg_le_of_boundedWeight` (`BoundedWeight T c A → ‖flucAvg‖ ≤ B`, uses only `0 ≤ t`, `∑ t ≤ 1` fields of the merged `BoundedWeight`), per DECISIONS §30 (weaker premise than `UniformWeight`).

Key targets, verbatim from the file:
```
-- LDE.lean:450
theorem eventually_le_W {d : ℕ} (sz : Sizes d) {c : ℝ} (hc : 0 < c) (hsz : sz.SizeTendsto)
    (hbw : sz.Bandwidth c) (p : ℕ) : ∀ᶠ n : ℕ in atTop, p ≤ sz.W n := by
-- LDE.lean:1099
theorem stochDom_normSq_Hflow_diag {d : ℕ} (sz : Sizes d) (hsz : sz.SizeTendsto) {t : ℕ → ℝ}
    (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n < 1) :
    sz.PrecPT (U := fun n => Vtx d (sz.L n) (sz.W n))
      (fun n i ω => ‖blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω) i i‖ ^ 2)
      (fun n i _ => svar d (sz.L n) (sz.W n) (sz.lam n) i i) := by
```
Both are in the "identical after renaming" set. Definitions used (`RBM3D/Defs/Sizes.lean:168-173`, `Defs/StochDomAt.lean:125`):
```
def Bandwidth (𝔠 : ℝ) : Prop := ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ (sz.W n : ℝ)
def SizeTendsto : Prop := Tendsto (fun n => ((sz.size n : ℕ) : ℝ)) atTop atTop
def PrecPT (ξ ζ : ∀ n, U n → SeqΩ sz → ℝ) : Prop := Path.PerTimeDomAt (seqP sz) sz.size ξ ζ
```
DECISIONS §29 (3)-(4) for `eventually_le_W`: conclusion `∀ᶠ n`; hypotheses are `0 < c`, `SizeTendsto`, `Bandwidth c` only (paper `Main_DEL_COND`, `1_2:359`); no constant depending on `W`, `L`, `lam`; no `L^d ≤ W^K`. `stochDom_normSq_Hflow_diag`: time window `0 ≤ t n < 1` as RBM2D; the conclusion is the `hLdiag` hypothesis of the merged `diag_bound_stochDom` (checked by the compiled `GiiOmegaSeq` example, §4); `stochDom_ldeRow/Col` likewise feed `entry_bound_stochDom`.

## 4. Hidden hypotheses, vacuity, cycles; compiled instances

* No hypothesis in a structure field: the targets take `Sizes d` (fields `L, W, lam, three_le_L, W_pos`) and explicit Props. `FlucBound` is a ported conclusion predicate, proved by `flucBound_env`, never a premise of a target.
* No cycle: imports are three merged `Green/*` files (§1); no import of `RBM3D`.
* External limit hypotheses `SizeTendsto`, `Bandwidth (1/6)` are discharged at `sz0` by merged theorems:
```
sz0_bandwidth : sz0.Bandwidth (1 / 6)
sz0_tendsto : sz0.SizeTendsto
def RBM.Gauss.SizesInst.sz0 : Sizes 3 :=
{ L := fun n => 4 * (n + 1), W := fun n => (2 * (n + 1)) ^ 5, lam := fun n => ((2 * (↑n + 1)) ^ 6)⁻¹, … }
```
* Compiled instances (in `LDE.lean`, namespace `RBM.Green.LDEInst`; compiled in §1 build):
  - `eventually_le_W_sz0 (p)` := `eventually_le_W sz0 (c := 1/6) (by norm_num) sz0_tendsto sz0_bandwidth p` and `eventually_le_W_sz0_million` (`p = 10^6`): `d = 3`, nondegenerate.
  - `stochDom_normSq_Hflow_diag_sz0` := `stochDom_normSq_Hflow_diag sz0 sz0_tendsto (t := fun _ => 1/2) …` (`0 ≤ 1/2 < 1` by `norm_num`).
  - `stochDom_ldeRow_sz0`, `stochDom_ldeCol_sz0` at `κ = 1`, `E ≡ 0`, `t ≡ 1/2`; an `example : GijOmegaSeq sz0 …` through `entry_bound_stochDom` with no hypothesis left; an `example : GiiOmegaSeq sz0 …` through `diag_bound_stochDom` with only `hLquad` (S1-12..S1-19 pin, not proved yet) as a section variable.
  - Nondegeneracy of the diagonal profile: `diag_variance_sz0` (`S_ii = 32^{-3}(1+6/64²)^{-1} > 0`); the preflight sample `d=3, L=3, W=2, g=1/2, u=1/2`: `integral_norm_Hflow_diag_pow_szT : ∫ ‖H_xx‖^4 = 3/1600` (private `szT`, constant sequence, used only for this moment identity).
* General-sequence elaboration (auditor scratch, compiled with exit 0):
```
example {d : ℕ} (sz : RBM.Gauss.Sizes d) (hsz : sz.SizeTendsto) (t : ℕ → ℝ) (h0 : ∀ n, 0 ≤ t n)
  (h1 : ∀ n, t n < 1) := stochDom_normSq_Hflow_diag sz hsz h0 h1
```

## 5. Paper deltas
Lean/RBM2D-pin differences and their coverage (prove report (d)):
* `card_Sblk_support` (`2d+1`, orientation) → `T2078a`.
* `Sblk2_diag_eq`, `Sblk_diag_pos` (`W^{-d}(1+2dg²)⁻¹`, `g` enters) → `T2078b`.
* `LDE_norm_flucAvg_le_of_boundedWeight` (bounded weight) → `T2078c`, relying on T2061a (DECISIONS §30).
* `card_blockAvg_support`, the `(sz.lam n)` argument of `svarF`: renaming R2-R4 (no delta needed). The paper does not state these lemmas (`3_5:37` cites `[YY_25]` Lemma 4.1 for `lem_GbEXP`); no further statement difference found.

## 6. Name clashes; observations
Name grep of the 64 declaration names of `LDE.lean` against non-private declarations in `main:RBM3D/*.lean`: `clashes on main: 0`.
Observations (no RETURN): prove report b.5 counts 44 RBM2D public declarations, the auditor's script 45 (it also counts `structure`/`def` lines), both find none dropped; RBM2D names with `d = 2` spelling are kept (`Sblk2_diag_eq`, `flucAvg_card_Z2_le_size`), flagged in prove report (d).

## Verdict per target
* `eventually_le_W` (FlucAvg:396): **PASS**.
* `stochDom_normSq_Hflow_diag` (LDE:659): **PASS**.
* Other ported public declarations (incl. `stochDom_ldeRow`, `stochDom_ldeCol`): **PASS**.

Overall: **PASS**. No dispatcher sign-off needed.
