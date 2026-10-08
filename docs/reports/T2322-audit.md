Auditor model: claude-opus-5-5

# T2322 audit (round 2, after repair round 1) — UN-31a `RBM3D/Universality/GUEPhase/Proc.lean`

Written Thu Oct  8 04:44:25 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2322-audit2`,
detached at `t/T2322` = `5bce253`; merge-base with `main` `e89ef53`. Scratch: `scratchpad/T2322/`.
Round 1 (`0d695a8`) returned one target, `gue_inv_W_le_loopMax`. Every other target passed. This round re-runs the
build, axioms, hygiene and check-file equality on the whole file and re-audits the repaired target.

## 1. Build, hygiene, diff, axioms
```
$ lake build RBM3D.Universality.GUEPhase.Proc        # started Thu Oct  8 04:42:03 UTC 2026
exit 0 ; lines matching "error": 0
✔ [3756/3756] Built RBM3D.Universality.GUEPhase.Proc (5.5s)
Build completed successfully (3756 jobs).
(no warning line mentions GUEPhase/Proc)
$ grep -nE "sorry|admit|native_decide|^\s*axiom " Proc.lean | wc -l
0
$ git diff --stat main...t/T2322
 RBM3D/Universality/GUEPhase/Proc.lean | 1126 +++++++++++++++++++++++++++++++++
 1 file changed, 1126 insertions(+)
$ lake env lean ax2.lean   # import ...GUEPhase.Proc; #print axioms of the 11 defs + 14 public theorems (25 lines)
ax exit 0
25 x "depends on axioms: [propext, Classical.choice, Quot.sound]" ; other lines: 0
$ lake env lean reg2.lean  # import RBM3D; import RBM3D.Universality.GUEPhase.Proc; #assert_rbm_axioms
reg exit 0 ; lines matching "error": 0
```
The diff adds one new file. No merged or frozen signature is touched.

## 2. Check-file equality (ticket acceptance)
```
$ python3 -I (defs.py) check.lean Proc.lean   # docstring + def text of check §2 vs file, whitespace-normalized
11 11 True
$ lake env lean ce2.lean  # check file + `import ...GUEPhase.Proc`, then for X in {gueLproc_nonneg, gueLproc_time, gueDev_succ_le}:
                          #   example (d : ℕ) (sz : RBM.Gauss.Sizes d) : RBM.Univ.GUEPhase.T2322Check.T2322_X sz := RBM.Univ.GUEPhase.X sz
ce exit 0 ; lines matching "error": 0
```

## 3. What changed since round 1 (script)
```
$ git diff -U0 0d695a8 5bce253 | grep '^@@'
@@ -34,2 +34,2 @@ On the size scale:                                  (module docstring)
@@ -45,3 +45,3 @@ What changes from `d = 2` ...                       (module docstring)
@@ -535,4 +535,4 @@ private theorem Proc_maxLoopPM_le_loopMax ...      (docstring of gue_inv_W_le_loopMax)
@@ -541 +541 @@ theorem gue_inv_W_le_loopMax ...                      (hell)
@@ -544 +544,2 @@ theorem gue_inv_W_le_loopMax ...                    (conclusion)
@@ -569 +570 @@ / @@ -571,4 +572,14 @@ theorem gue_inv_W_le_loopMax ... (proof)
@@ -1030,3 +1041,3 @@ / @@ -1035 ... @@ -1039 ... @@ -1043,3 +1055,4 @@  (the two Ward instances)
```
No other statement changed. The round-1 script comparison (14 public theorems vs RBM2D `Proc.lean:1-860` under the
ticket's renaming) therefore still holds for the 13 targets that passed then.

## 4. `gue_inv_W_le_loopMax`: statement against the pin and the round-1 repair list
```
Proc.lean:539  theorem gue_inv_W_le_loopMax {L W : ℕ} [NeZero L] [NeZero W]
                   {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) {E u : ℝ}
                   (hE : |E| < 2) (hu : u < 1) {g : ℝ} (hell : (L : ℝ) ^ 2 * (1 - u) ≤ g ^ 2) {δ : ℝ}
                   (hΩ : RBM.Green.GoodEvent (RBM.Green.greenBlk d L W E u M true) (mE E) δ)
                   (hδ : δ ≤ (mE E).im / 2) :
                   ((W : ℝ)⁻¹) ^ d ≤
                     2 * (L : ℝ) ^ (d - 2) * g ^ 2 * RBM.Ind.loopMax d L W (blockMat d L W M) (zt E u) 2
Bootstrap.lean:148 ellT_eq_L {L : ℕ} {g t : ℝ} (hg : 0 ≤ g) (ht : t < 1) (h : (L : ℝ) ^ 2 * (1 - t) ≤ g ^ 2) : RBM.ellT L g t = L
EntryDet.lean:354  inv_N_le_maxLoopPM ... (hz : 0 < (zt E u).im) (hΩ : GoodEvent (greenBlk d L W E u M true) m δ) (hδ : δ ≤ m.im / 2) :
                   m.im / (2 * ((((W * L) ^ d : ℕ) : ℝ) * (zt E u).im)) ≤ maxLoopPM d L W E u M
```
- `hell` is now exactly the `ellT_eq_L` condition, with `t ↦ u`. The pin asks for this.
- Exponent: with `η = (1-u) Im m`, `inv_N_le_maxLoopPM` gives `W^{-d} ≤ 2 L^d (1-u) maxLoopPM`. Then `L^d ≤ L^{d-2} L²`
  (because `L ≥ 1`, and `d ≤ (d-2)+2` holds in ℕ for every `d`) and `hell` give `W^{-d} ≤ 2 L^{d-2} g² L₂`. The
  conclusion is the bound "exactly as `inv_N_le_maxLoopPM` gives it" on the `ellT_eq_L` window. It loses nothing beyond
  `L^d(1-u) ≤ L^{d-2} g²`, which is an equality when `L²(1-u) = g²`. At `d = 2`, `g = 1` it is the RBM2D statement
  (`Proc.lean:519`).
- `hd` is not added, and none is needed: for `d < 2`, `d - 2 = 0` and `L^d ≤ L²` still holds.
- The round-1 form `L^d(1-u) ≤ 1` is no longer in the file (`grep "L : ℝ) ^ d \* (1 - u) ≤ 1"`: 0 hits in statements).
- Limit check of the factor chain (python3, the GUE-phase window `L²(1-t) = 1` from round 1, plus the instance data):
```
d=3 L=3 W=2 u=0.000000 g=3: L^2(1-u)=9.0000<=g^2=9:True  2L^d(1-u)=54.0000<=2L^(d-2)g^2=54.0000:True
d=3 L=8 W=4 u=0.984375 g=1: L^2(1-u)=1.0000<=g^2=1:True  2L^d(1-u)=16.0000<=2L^(d-2)g^2=16.0000:True
d=3 L=16 W=2 u=0.996094 g=1: L^2(1-u)=1.0000<=g^2=1:True  2L^d(1-u)=32.0000<=2L^(d-2)g^2=32.0000:True
d=4 L=5 W=3 u=0.900000 g=1.6: L^2(1-u)=2.5000<=g^2=2.5600000000000005:True  2L^d(1-u)=125.0000<=2L^(d-2)g^2=128.0000:True
```
  On the windows where round 1 showed the old hypothesis fails (`L = 8`, `16`, `1-t = L^{-2}`), the repaired lemma applies.

## 5. Hidden hypotheses, vacuity, cycles
No `structure` or `class` is introduced, no new `Prop` is assumed, and there is no registry line. `g` is a free real, and
`hell` is its only constraint. The other premises are unchanged and in the signature. `hΩ` is the deterministic
`GoodEvent` of merged `inv_N_le_maxLoopPM`, not an external input. The imports are the eight merged modules pinned by the
ticket (equal to the check file's, round 1). Nothing imports `RBM3D` or T2323.

## 6. Compiled nonempty instances (`ProcInst`, `Proc.lean:920-1124`; all compile, §1)
New Ward instance (`Proc.lean:1054-1063`). Every hypothesis is discharged at `d = 3`, `L = 3`, `W = 2`, `E = 0`,
`u = 0`, `g = 3`, `δ = 0`, `M = 0`:
```
example : (((2 : ℕ) : ℝ)⁻¹) ^ 3 ≤
    2 * ((3 : ℕ) : ℝ) ^ (3 - 2) * (3 : ℝ) ^ 2 *
      RBM.Ind.loopMax 3 3 2 (blockMat 3 3 2 (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ)) (zt 0 0) 2 :=
  gue_inv_W_le_loopMax (L := 3) (W := 2) (E := 0) (u := 0) (g := 3) (δ := 0)
    Matrix.isHermitian_zero (by norm_num) (by norm_num) (by norm_num)
    (by
      rw [RBM.Green.greenBlk_time_zero (by norm_num)]
      intro x y
      by_cases h : x = y <;> simp [h])
    (by rw [mE_zero_im]; norm_num)
```
This instance is nondegenerate: `L = 3`, `N = 216`, `hell` is tight (`9 = 9`), and `g` is not large. A second instance
(`:1044-1052`, `L = 3`, `W = 4`, `u = 26/27`, `g = 1`) discharges `hE`, `hu`, `hell`, `hδ` and keeps `hΩ` for an abstract
Hermitian `M`. The instances of the other 24 targets did not change since round 1, where they were verified (structural
facts and `gueDev_succ_le` on `SizesInst.sz0`, `d = 3`; tent/interp on the grid `4/5, 9/10, K = 4`; `gueLoopMax_*` on
`Vtx 3 3 2`; `norm_egtNGUE_le` at `d = 3, L = 3, W = 2`). They compile in this build.

## 7. Paper deltas
Prove report (d) T2322a has been reworded. It now records `hell : L²(1-u) ≤ g²` with the conclusion
`(W⁻¹)^d ≤ 2 L^{d-2} g² L₂`, against `[YY_25]`/RBM2D `W^{-2} ≤ 2 L₂` under `L²(1-u) ≤ 1`, and it explains where the factor
comes from. It covers the only Lean/source statement difference. `norm_egtNGUE_le` `(WL)² ↦ (WL)^d` is the
ticket-prescribed renaming (`N = (WL)^d`), so no delta is needed.

## 8. Observations (no effect on statement, instance, build, axioms or delta coverage)
- Prove report lines 47, 51, 69, 80 and 252 (section (a)(i) C1, the (a) Ward rows, b.7 item) still describe the replaced
  `L^d(1-u) ≤ 1` form. Line 69 also says "`M = 0` is NOT a witness"; that is true only at `u = 26/27`, and the new
  instance uses `u = 0`. The report's repair section (lines 282-299) marks these parts as describing `0d695a8`.

## 9. Verdicts
- Eleven definitions (check §2), `gueLproc_nonneg`, `gueLproc_time`, `gueDev_succ_le` (pinned): **PASS**.
- `gueDproc_nonneg`, `gueLproc_continuousOn`, `gueDproc_continuousOn`, `gueLproc_le`, `gueDproc_le`, `gueLproc_odd`,
  `gueDproc_time`, `gueLoopMax_odd_succ_le`, `gueLoopMax_four_mul_le`, `norm_egtNGUE_le`: **PASS** (unchanged since round 1).
- `gue_inv_W_le_loopMax`: **PASS**. Round-1 repair items 1–3 are met (§4, §6, §1–§2, §7).

Ticket verdict: **PASS**. No dispatcher sign-off needed.
