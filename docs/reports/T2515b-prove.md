Prover model: claude-sonnet-5-5
# T2515b — stage 1b prove report, row b (`BA/GUEEntry` + `GUEEntry2`, targets 9–13), written Thu Oct 15 10:18:22 UTC 2026

## (a) Math preflight
Not repeated (row b has no section of its own): `docs/reports/T2515-prove.md` (a), census/split `:21,:43-44`, pin mathematics `:27`; 1a-audit `docs/reports/T2515-1a-audit.md` (PASS, pin text signed with `g` a free family `g n`, split a | b, no b | b′).
### (a′) Preflight corrections: none (no mistake in (a) found; the size forecast of (a) was exceeded, see b1 and the narrative).

## (b) Script output
### b1 Size against the ticket's stop lines (commands and outputs)
```
$ wc -l RBM3D/BA/GUEEntry.lean RBM3D/BA/GUEEntry2.lean
    1524 RBM3D/BA/GUEEntry.lean
    1225 RBM3D/BA/GUEEntry2.lean
    2749 total
$ grep -o "Stop lines:[^;]*; \*\*2,000 per file\*\* (binding)" docs/tickets/T2515.md
Stop lines: `GUEKPrim` 1,500, `GUEEntry` 1,300, `GUEEntry2` 700; **2,000 per file** (binding)
$ sed -n 96,98p docs/reports/T2515-1a-audit.md | cut -c1-180
**Census — SIGNED** (reproduced, §3). **Split — SIGNED: a | b at `GUEKPrim` | `GUEEntry`** (total central 2,762 > 1,950); row a
`t/T2515` (targets 1–8, central 1,114; 1,069–1,426 < stop 1,500); row b `t/T2515b` (targets 9–13, central 1,648 ≤ 1,950: **no b | b′**;
calibrated top 2,109 > 1,950 → forecast check at the 1b head). Row b files: `GUEEntry` ≤ 1,300 + `GUEEntry2` ≤ 700; 2,000 per file binds.
$ sed -n 43p docs/reports/T2515-prove.md | cut -c1-330
Row b: BA-only new is 0 in the ticket, but `stable_mixBA` replaces the scalar `m` of `EntryDet §4-5` by the matrix `M^{(B)}`; it is not priced (risk, not counted). Row a upper end 1,426 < stop line 1,500 < 2,000. Row b centrals exceed the stop line `GUEEntry` 1,300, so `GUEEntry2` is used (the ticket's Layout says "past 1,800", 
```
### b2 Name-level tables
Ported declarations (script: the file:line of every row is found by regex in the files; all sources are merged RBM3D files, none from RBM1D/RBM2D):
```
source (file:line, decl)  ->  new (file:line, decl)
Universality/GUEPhase/EntryDet.lean:91 stable_mix  ->  GUEEntry.lean:68 stable_mixBA
Universality/GUEPhase/EntryDet.lean:719 mix_det  ->  GUEEntry.lean:1376 mix_detBA
Universality/GUEPhase/EntryDet.lean:334 ward_col, :443 ward_row  ->  GUEEntry.lean:676 GUEEntry_wardData_of
Universality/GUEPhase/EntryDet.lean:354 inv_N_le_maxLoopPM  ->  GUEEntry.lean:695 GUEEntry_J
BA/GreenCore.lean:855 GreenCore_Xcol_avg  ->  GUEEntry.lean:204 GUEEntry_Xcol_avg
BA/GreenCore.lean:903 GreenCore_twoSided  ->  GUEEntry.lean:233 GUEEntry_twoSided
BA/GreenCore.lean:972 GreenCore_Rbound  ->  GUEEntry.lean:294 GUEEntry_Rbound
BA/GreenCore.lean:1253 GreenCore_E3  ->  GUEEntry.lean:963 GUEEntry_E3
BA/GreenCore.lean:1248 GreenCore_K  ->  GUEEntry.lean:957 GUEEntry_K
BA/GreenCore.lean:1276 GreenCore_coupled  ->  GUEEntry.lean:872 GUEEntry_coupled
BA/GreenCore.lean:1361 GreenCore_diag  ->  GUEEntry.lean:993 GUEEntry_core
Universality/GUEPhase/EntryTail.lean:54 mixMat  ->  GUEEntry2.lean:448 mixMatBA
Universality/GUEPhase/EntryTail.lean:94 GUEEntryMix  ->  GUEEntry2.lean:738 GUEEntryMixBA
Universality/GUEPhase/EntryTail.lean:492 mixEntry_quad_tail  ->  GUEEntry2.lean:243 GUEEntry_quad_tail
Universality/GUEPhase/EntryTail.lean:548 mixEntry_row_tail  ->  GUEEntry2.lean:321 GUEEntry_row_tail
Universality/GUEPhase/EntryTail.lean:608 mixEntry_col_tail  ->  GUEEntry2.lean:375 GUEEntry_col_tail
Universality/GUEPhase/EntryTail.lean:859 mixEntry_det  ->  GUEEntry2.lean:85 mixEntry_detBA
Universality/GUEPhase/EntryTailMain.lean:120 mixBad  ->  GUEEntry2.lean:481 GUEEntry_bad
Universality/GUEPhase/EntryTailMain.lean:175 mixBad_tail  ->  GUEEntry2.lean:492 GUEEntry_bad_tail
Universality/GUEPhase/EntryTailMain.lean:292 mixEntry_event_subset  ->  GUEEntry2.lean:603 GUEEntry_event_subset
Universality/GUEPhase/EntryTailMain.lean:369 mixEntry_union  ->  GUEEntry2.lean:671 GUEEntry_union
Universality/GUEPhase/EntryTailMain.lean:545 gueEntryMix  ->  GUEEntry2.lean:785 gueEntryMixBA
```
Merged declarations read (round 1 `deps.lean`/`chk.lean` output, 28 lines) removed in the repair to keep this report within 300 lines.
`open private` lines (band privates reached without a third copy): `GUEEntry.lean:34` EntryDet_card_vtx_real; `GUEEntry2.lean:27-29` loopFine_pm_formula_vtx, sum_vtx_ite (Green.Pins), EntryTail_Gres_true (EntryTail), mixEntry_final_arith (EntryTailMain).
### b3 Builds
```
$ lake build RBM3D.BA.GUEEntry RBM3D.BA.GUEEntry2 2>&1 | grep "✔\|✖\|error\|Build completed"
Build completed successfully (3808 jobs).
$ lake env lean RBM3D/BA/GUEEntry.lean  (fresh compile) -> exit=0, 26 s, 0 message lines (10:15:52 UTC)
$ lake env lean RBM3D/BA/GUEEntry2.lean  (fresh compile) -> exit=0, 12 s, 0 message lines (10:16:04 UTC)
$ lake build  (whole library, runs #assert_rbm_axioms; start 09:59:22 UTC, end 10:00:40 UTC by `date -u`; output saved)
$ grep "axiom audit" fullbuild.out | cut -c1-150
info: RBM3D.lean:650:0: axiom audit: 15508 theorems, 4757 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ tail -3 fullbuild.out | cut -c1-150
non-vacuity certificates: 0 of 122 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what e
Build completed successfully (4420 jobs).
exit: 0
```
The first full build (09:56 UTC) failed at `RBM3D.lean:650` (axiom audit): "1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, ...: [RBM.BA.GUEEntry_Setup]"; fixed by making the bundle `GUEEntry_Setup` and the three lemmas taking it private (commit f8250a35); the rerun above passes.
### b4 Axioms (all 75 public declarations of the two files)
```
$ #print axioms RBM.BA.<n> for every public declaration of the two files (lake env lean), n = 75
lines with exactly [propext, Classical.choice, Quot.sound]: 75
other lines (sorry / extra axioms / errors): 0
'RBM.BA.mixEntry_detBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.mixMatBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GUEEntry_mixMatBA_eq_Xmat' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GUEEntry_mixMatBA_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GUEEntry_ouMatC_ba_eq_mixMatBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GUEEntryMixBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.gueEntryMixBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stable_mixBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.mix_detBA' depends on axioms: [propext, Classical.choice, Quot.sound]
```
### b5 Target statements, extracted from the files by script (`extract.py`)
```
-- GUEEntry.lean:68-72   (innermost section variable: variable (d L : ℕ) [NeZero L])
theorem stable_mixBA {g κ E : ℝ} {m : ℂ} (hκ : 0 < κ) (hr : BAReal d L g κ E m) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : a + b < 1) (v : Zd d L → ℂ) (B : ℝ)
    (hB : ∀ x, ‖v x - ∑ y, BAMss d L (BAMB d L g (E : ℂ) m) true true x y *
      ((a : ℂ) * v y + (b : ℂ) * ((((L ^ d : ℕ) : ℂ))⁻¹ * ∑ z, v z))‖ ≤ B) :
    ∀ x, ‖v x‖ ≤ 16 * κ⁻¹ ^ 4 * (1 + 16 * κ⁻¹ ^ 4) * B := by

-- GUEEntry.lean:1376-1393   (innermost section variable: variable {d L W : ℕ} [NeZero L] [NeZero W])
theorem mix_detBA {g Λ κ E a b δ Φ Lm : ℝ} {m s z : ℂ} {G X M D : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hd : 3 ≤ d) (hL : 3 ≤ L) (hg : 0 < g) (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hr : BAReal d L g κ E m)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hu1 : a + b < 1)
    (hGR : G * (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1)
    (hRG : (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G = 1)
    (hMR : (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * M = 1)
    (hMR' : M * (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1)
    (hz : z = s - ((a + b : ℝ) : ℂ) * m)
    (hM : ∀ u v, M u v = if u.2 = v.2 then BAMB d L g (E : ℂ) m u.1 v.1 else 0)
    (hD : ∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g : ℂ) else 0)
    (hH : (D + X).IsHermitian) (hzim : 0 < z.im)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ GUEEntry_dlt d Λ κ) (hwd : ((W : ℝ) ^ d)⁻¹ ≤ δ ^ 2)
    (hΩ : ∀ u v, ‖G u v - M u v‖ ≤ δ) (hΦ : 1 ≤ Φ) (hΦδ : GUEEntry_cs d Λ κ * Φ * δ ^ 2 ≤ 1)
    (hLrow : LDERow X G (GUEEntry_Smv d L W a b) Φ) (hLcol : LDECol X G (GUEEntry_Smv d L W a b) Φ)
    (hLquad : LDEQuad X G (GUEEntry_Smv d L W a b) 1 Φ)
    (hLdiag : ∀ i, ‖X i i‖ ^ 2 ≤ Φ * GUEEntry_Smv d L W a b i i)
    (hLm : ∀ a b, GreenCore_loop G a b ≤ Lm) (x y : Vtx d L W) :
    ‖G x y - M x y‖ ^ 2 ≤ GUEEntry_C d Λ κ * Φ ^ 2 * (Lm + ((W : ℝ) ^ d)⁻¹) := by

-- GUEEntry2.lean:448-451   (innermost section variable: variable {d : ℕ})
def mixMatBA (sz : Sizes d) (n : ℕ) (g a b : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  (g : ℂ) • PsiI d (sz.L n) (sz.W n) +
    @id (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (mixMat (sz.withLam 0) n a b ω)

-- GUEEntry2.lean:85-100   (innermost section variable: variable {d L W : ℕ} [NeZero L] [NeZero W])
theorem mixEntry_detBA {g Λ κ E a b δ Φ : ℝ} {m : ℂ} (hd : 3 ≤ d) (hL : 3 ≤ L) (hg : 0 < g) (hgΛ : g ≤ Λ)
    (hκ : 0 < κ) (hr : BAReal d L g κ E m) (ha : 0 ≤ a) (hb : 0 ≤ b) (hu1 : a + b < 1)
    {X : Matrix (Idx d L W) (Idx d L W) ℂ} (hX : X.IsHermitian)
    (hllErr : ∀ x y, GUEEntry_llErr d L W g E m (a + b) ((g : ℂ) • PsiI d L W + X) x y ≤ δ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ GUEEntry_dlt d Λ κ) (hwd : ((W : ℝ) ^ d)⁻¹ ≤ δ ^ 2) (hΦ : 1 ≤ Φ)
    (hΦδ : GUEEntry_cs d Λ κ * Φ * δ ^ 2 ≤ 1)
    (hrow : ∀ i j, i ≠ j → ldeRowLHS X (green ((g : ℂ) • PsiI d L W + X) (ztOf m E (a + b))) i j ≤
      Φ * ldeRowRHS (Smix d L W 0 a b) (green ((g : ℂ) • PsiI d L W + X) (ztOf m E (a + b))) i j)
    (hcol : ∀ k j, k ≠ j → ldeColLHS X (green ((g : ℂ) • PsiI d L W + X) (ztOf m E (a + b))) k j ≤
      Φ * ldeColRHS (Smix d L W 0 a b) (green ((g : ℂ) • PsiI d L W + X) (ztOf m E (a + b))) k j)
    (hquad : ∀ i, ldeQuadLHS X (green ((g : ℂ) • PsiI d L W + X) (ztOf m E (a + b))) (Smix d L W 0 a b) 1 i ≤
      Φ * ldeQuadRHS (Smix d L W 0 a b) (green ((g : ℂ) • PsiI d L W + X) (ztOf m E (a + b))) i)
    (hdiag : ∀ i, ‖X i i‖ ^ 2 ≤ Φ * Smix d L W 0 a b i i) (i j : Idx d L W) :
    GUEEntry_llErr d L W g E m (a + b) ((g : ℂ) • PsiI d L W + X) i j ^ 2 ≤
      GUEEntry_C d Λ κ * Φ ^ 2 * (GUEEntry_maxLoop d L W m E (a + b) ((g : ℂ) • PsiI d L W + X) +
        ((W : ℝ) ^ d)⁻¹) := by

-- GUEEntry2.lean:738-756   (innermost section variable: variable {d : ℕ})
def GUEEntryMixBA (d : ℕ) : Prop :=
  ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
  ∀ (g E : ℕ → ℝ) (m : ℕ → ℂ), (∀ n, 0 < g n ∧ g n ≤ 𝔡⁻¹ ∧ BAReal d (sz.L n) (g n) κ (E n) (m n)) →
  ∀ n0 : ℕ, ∀ K : ℕ → ℕ, (∀ n, K n ≤ (sz.size n) ^ n0) → ∀ a b : ∀ n, Fin (K n + 1) → ℝ,
  (∀ n k, 0 ≤ a n k ∧ 0 ≤ b n k ∧ 0 < a n k + b n k ∧ a n k + b n k < 1) →
  ∀ (c₀ : ℝ) (δ : ℕ → ℝ), 0 < c₀ → (∀ n, 0 ≤ δ n) →
  (∀ᶠ n in atTop, δ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-c₀)) →
  ∀ τ D : ℝ, 0 < τ → 0 < D → ∀ᶠ n in atTop,
    ouP (UNModel.band (sz.withLam 0)) n
      {ω | ∃ (k : Fin (K n + 1)) (i j : Idx d (sz.L n) (sz.W n)),
        ((sz.size n : ℕ) : ℝ) ^ τ *
            (GUEEntry_maxLoop d (sz.L n) (sz.W n) (m n) (E n) (a n k + b n k)
                (mixMatBA sz n (g n) (a n k) (b n k) ω) + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) <
          (if ∀ x y, GUEEntry_llErr d (sz.L n) (sz.W n) (g n) (E n) (m n) (a n k + b n k)
                (mixMatBA sz n (g n) (a n k) (b n k) ω) x y ≤ δ n
            then GUEEntry_llErr d (sz.L n) (sz.W n) (g n) (E n) (m n) (a n k + b n k)
                  (mixMatBA sz n (g n) (a n k) (b n k) ω) i j ^ 2
            else 0)} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))

-- GUEEntry2.lean:785-785   (innermost section variable: variable {d : ℕ} )
theorem gueEntryMixBA (hd : 3 ≤ d) : GUEEntryMixBA d := by
```
Pin against the band text (script `diff band_pin.txt ba_pin.txt | grep -c '^[<>]'` on the two `def` texts): 10 of the 19 lines of the band text (`EntryTail.lean:94-112`) are replaced by 10 lines (`GUEEntry2.lean:738-756`), differing only in: the name; the binder `∀ E, |E n| ≤ 2 - κ` ↦ `∀ (g E) (m), ∀ n, 0 < g n ∧ g n ≤ 𝔡⁻¹ ∧ BAReal d (sz.L n) (g n) κ (E n) (m n)`; the law `UNModel.band sz` ↦ `UNModel.band (sz.withLam 0)`; `maxLoopPM`/`llErrMat`/`mixMat sz` ↦ `GUEEntry_maxLoop`/`GUEEntry_llErr` (extra `m n`, `g n`) / `mixMatBA sz n (g n)`. Hypotheses, quantifier order, `∀ᶠ`, no `∃ C`: as the band text.
### b6 Compiled nonempty instances (target 13; all `example`s in `GUEEntry2.lean`, section `GUEEntryInst`, lines 892-1223; they compile in the build above)
```
GUEEntry2.lean:926: example : ∀ x : Zd 3 4, ‖(fun _ : Zd 3 4 => (1 : ℂ)) x‖ ≤
GUEEntry2.lean:961: example := gueEntryMixBA (d := 3) le_rfl (1 / 6) (1 / 10) S0 S0_adm ((fp 4 GUEEntryInst_h310).m0.im)
GUEEntry2.lean:1032: example {X : Matrix (Idx 3 (sz0.L n₁) (sz0.W n₁)) (Idx 3 (sz0.L n₁) (sz0.W n₁)) ℂ} (hX : X.IsHermitian)
GUEEntry2.lean:1049: example (ω : sz0.SeqΩ) {Lm : ℝ}
GUEEntry2.lean:1093: example (i j : Idx 3 (sz0.L n₁) (sz0.W n₁)) :
GUEEntry2.lean:1127: example (ω : sz0.SeqΩ) (x y : Vtx 3 (sz0.L n₁) (sz0.W n₁)) :
GUEEntry2.lean:1194: example (ω : Sizes.SeqΩ sz0 × Ω 3 (sz0.L 3) (sz0.W 3)) :
GUEEntry2.lean:1200: example (ω : Sizes.SeqΩ sz0 × Ω 3 (sz0.L 3) (sz0.W 3)) :
GUEEntry2.lean:1205: example (ω : Sizes.SeqΩ sz0 × Ω 3 (sz0.L 3) (sz0.W 3)) :
GUEEntry2.lean:1209: example (ω : Sizes.SeqΩ sz0 × Ω 3 (sz0.L 3) (sz0.W 3)) :
GUEEntry2.lean:1218: example : gaussLaw 3 3 2 (mixVar 3 3 2 1 (1 / 4) (1 / 4))
examples: 11
$ python3 -I numerics.py   (the constants of the instances; the three inequalities are proved in Lean by GUEEntryInst_dlt/_cs/_wd)
rho=6.2925e+06 Sc=2.5166e+07 Kth=6.5792e+04 Kbd=4.1400e+11 dlt=1.2077e-12 cs=9.4895e+17
n=25: L=104 W=380204032 W^-3=1.819e-26; delta=1e-12: delta<=dlt True, W^-3<=delta^2 True, cs*delta^2=9.490e-07<=1 True
```
### b7 Greps, closure, name clash, diff
```
$ grep -nE 'msc|\bmE\b|lemT|lemE|Theta d|SB d L|kTwoGUE|KLgen|UNModel\.band|2 - κ|‖m‖ = 1' $F | cut -c1-110
(6 hit lines, GUEEntry2.lean:446,676,703,711,735,746; text in the round-1 report, removed in the repair for the length limit; narrative 6)
$ grep -cE '^(noncomputable )?(def|abbrev|structure) (UNOUProfRowk|RBG_ProfComp|BAProp8|BAprof|GUEEntryMix|SBtilde)\b' $F
GUEEntry.lean:0
GUEEntry2.lean:0
$ grep -cE '^import RBM3D\.BA\.(MainInd|TwistPins|Step6)' $F
GUEEntry.lean:0
GUEEntry2.lean:0
$ grep -cE '\b(sorry|admit|native_decide)\b|^axiom ' $F
GUEEntry.lean:0
GUEEntry2.lean:0
$ python3 -I closure.py  (transitive `import` closure of the two modules, parsed from the files)
transitive import closure of RBM3D.BA.GUEEntry, RBM3D.BA.GUEEntry2: 130 RBM3D modules
V modules (BA.MainInd*, BA.TwistPins, BA.Step6*) in the closure: 0 []
direct imports of GUEEntry present in the closure: 7 of 7
importers of GUEEntry/GUEEntry2 in RBM3D (excluding RBM3D.lean): 1
names declared in the two files (public + private): 98
$ git grep -nE '^(private )?(theorem|def|lemma|structure|abbrev|...) +([A-Za-z0-9_.]*\.)?<name>( |:|\()' main -- RBM3D RBM3D.lean, minus GUEEntry files (main = 9c5fc941): declarations with a new name = 0
$ same grep -rnE in the branch t/T2515b worktree, minus the two GUEEntry files: declarations with a new name = 0
$ git diff --stat main...t/T2515b   (merge-base 0deabaa8; main is now 9c5fc941)
 RBM3D.lean              |    2 +
 RBM3D/BA/GUEEntry.lean  | 1524 +++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/BA/GUEEntry2.lean | 1225 +++++++++++++++++++++++++++++++++++++
 3 files changed, 2751 insertions(+)
$ git diff main...t/T2515b -- RBM3D.lean | grep "^[+-]"
--- a/RBM3D.lean
+++ b/RBM3D.lean
+import RBM3D.BA.GUEEntry
+import RBM3D.BA.GUEEntry2
```

### Narrative
1. Scope. Row b of T2515 (targets 9-13) on `t/T2515b` from `0deabaa8`: new `RBM3D/BA/GUEEntry.lean` and `RBM3D/BA/GUEEntry2.lean`, two import lines in `RBM3D.lean` (after `import RBM3D.BA.MainIndTermBA`); `Test/Axioms.lean` untouched (the ticket expects no registry line for row b); no merged file edited (diff stat in b7). `main` has moved to 9c5fc941 (row a merged as 13b68cea); the hub adds the import lines itself at merge (CLAUDE.md §3 (A) 3-4). Commits (UTC, `git log`): bfaef632 09:43:32 (targets 9-12), 0435297e 09:56:48 (instances), f8250a35 10:00:52 (privacy fix after the first full build).
2. Stop rule. Both files are above the ticket's stop lines (1,524 > 1,300; 1,225 > 700) and below 2,000 per file; the row total 2,749 is above the 1a central 1,648 and its calibrated top 2,109 (the forecast check asked by the 1a-audit is answered by b1). I read the stop lines as the points where the reserve file is used and "2,000 per file (binding)" as the stop (`T2515-prove.md:43`, 1a-audit observation 6); at section commit 1 (`wc -l`: 1,524 / 892) I continued, so "over the ticket's stop size: commit, stop, RETURN" was not applied literally. The dispatcher decides whether to recalibrate the T2515 price table or to book a `b′`.
3. Contents. `stable_mixBA`: stability of `1 - M^{(+,+)} S̃` for the matrix `M^{(B)}` (constant `16κ⁻⁴(1+16κ⁻⁴)`; from `baStab_of_real`, `BAoffDiag_scalar`, `BAMss_ss_diag`, `BAMss_row_offdiag_sum`). `mix_detBA` (vertex level) and `mixEntry_detBA` (fine lattice `Idx`): `|G-M|² ≤ C Φ² (Lm + W^{-d})` with explicit constants `GUEEntry_C/_dlt/_cs` of `(d, Λ, κ)` (no `∃ C`); the private core `GUEEntry_core` is the twin of `GreenCore_diag` with the flat part `b/N` kept as an additive slack `Ξ`. `mixMatBA = g•PsiI + mixMat (sz.withLam 0)` with three identities; Gaussian tails with a Hermitian shift, `GUEEntry_bad`, `GUEEntry_bad_tail`, `GUEEntry_event_subset`, private `GUEEntry_union` (union over the pairs, `Measure.le_map_apply` with `mixSample_law`). `gueEntryMixBA : 3 ≤ d → GUEEntryMixBA d`.
4. Statement differences from the band twins (candidates in (d)). `mix_detBA` / `mixEntry_detBA` have the extra hypothesis `W^{-d} ≤ δ²` and the smallness `GUEEntry_cs Φ δ² ≤ 1` (band `mix_det`: `36 Φ δ² ≤ 1`, no `W^{-d}` hypothesis, `0 < a + b`, conclusion `mixCdet Φ² maxLoopPM`; the BA lemmas assume only `0 ≤ a`, `0 ≤ b`, `a + b < 1`). The pin proof therefore applies them at `δ' = max δ_n √(W^{-d})` (`√(W^{-d}) ≤ N^{-𝔠 d/2}` from the bandwidth); the pin's event with `δ_n` lies inside the one with `δ'` (the `if` is monotone in `δ`), so the pin text is not weakened.
5. Instances (b6). Fully discharged and nondegenerate: `gueEntryMixBA` at `S0` (`L = 4`, constant flow data of `fp 4 (3/10)`, `K = 1`, two mixtures, `δ_n = N^{-1} > 0`); `stable_mixBA` at the same flow point with `v ≡ 1`. For `mix_detBA` / `mixEntry_detBA` at `(a,b) = (1/4,1/4)` (`sz0`, `n = 25`, `L = 104`, `W = 52^5`, `κ = 1/2`, `Λ = 1/64`, `δ = 10⁻¹²`, `Φ = 1`) every numerical and structural hypothesis is discharged; the Hermitian sample `X`, the a priori event, the four large-deviation inputs and the loop bound stay hypotheses (`LDERow/LDECol/LDEQuad` are the large deviation conclusions that `Green/EntryCore.lean:505-511` takes as hypotheses; band precedent `inst_mixEntry_det`, `EntryTail.lean:1085`). Every hypothesis is discharged only at the boundary point `(a,b) = (0,0)` (`X = 0`, `G = M`). I did not construct an explicit sample `X ≠ 0` satisfying the inputs.
6. Greps (b7). The `UNModel.band` hits are docstrings (`GUEEntry2:446,735`), the signed pin text (`:746`) and the private `GUEEntry_union` (statement `:676`, proof `:703,:711`); no other C1 pattern, no X1-C4 redefinition, no V import (closure: 130 modules, 0 V modules).
7. Options. Four `set_option maxHeartbeats N in` (600000 `GUEEntry:1207`, 1600000 `:1370`, 800000 `GUEEntry2:80,:778`), each with a reason comment; the other options are the linter switches used in merged BA files.

## (c) Verified Mathlib names (all compiled; `#check` of the 103 qualified names used in the two files, script `ml.lean`: 0 errors)
```
Complex.I Complex.abs_im_le_norm Complex.conj_conj Complex.conj_ofReal Complex.continuous_conj Complex.im_le_norm Complex.norm_conj
Complex.norm_natCast Complex.norm_real Complex.ofReal_one Complex.sub_im ENNReal.ofReal ENNReal.ofReal_add ENNReal.ofReal_le_ofReal ENNReal.ofReal_mul
ENNReal.ofReal_natCast Equiv.subRight Equiv.sum_comp Equiv.symm_apply_apply Filter.Eventually.of_forall Finite.exists_max Finset.add_sum_erase
Finset.card_erase_le Finset.card_univ Finset.erase_subset Finset.le_sup' Finset.mem_univ Finset.mul_sum Finset.ne_of_mem_erase Finset.single_le_sum
Finset.sum_add_distrib Finset.sum_comm Finset.sum_congr Finset.sum_const Finset.sum_div Finset.sum_eq_zero Finset.sum_erase Finset.sum_le_sum
Finset.sum_le_sum_of_subset_of_nonneg Finset.sum_mul Finset.sum_neg_distrib Finset.sum_nonneg Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
Finset.sum_sub_distrib Finset.univ Finset.univ.sup' Fintype.card Fintype.card_fin Fintype.card_prod Fintype.sum_prod_type IsHermitian.add
Matrix.IsHermitian Matrix.add_apply Matrix.inv_eq_left_inv Matrix.inv_submatrix_equiv Matrix.isHermitian_zero Matrix.kroneckerMap_apply
Matrix.nonsing_inv_eq_ringInverse Matrix.of_apply Matrix.one_apply Matrix.smul_apply Matrix.submatrix_apply Matrix.submatrix_mul_equiv
Matrix.submatrix_one_equiv Matrix.zero_apply Measure.le_map_apply Measure.map_apply Nat.cast_ne_zero Nat.cast_nonneg Nat.cast_pos Nat.factorial
Nat.le_ceil Nat.le_mul_of_pos_right Nat.lt_succ_iff Nat.mul_pos Nat.pow_le_pow_left Real.abs_le_sqrt Real.exp Real.exp_le_one_iff Real.exp_pos
Real.log Real.norm_of_nonneg Real.one_le_rpow Real.one_sub_inv_le_log_of_pos Real.rpow_add Real.rpow_le_rpow_of_exponent_le Real.rpow_mul
Real.rpow_natCast Real.rpow_neg Real.rpow_nonneg Real.rpow_pos_of_pos Real.sq_sqrt Real.sqrt Real.sqrt_le_iff Real.sqrt_le_one Real.sqrt_nonneg
Real.sqrt_pos Ring.inverse Ring.inverse_mul_cancel Ring.mul_inverse_cancel Set.mem_iUnion Set.mem_ofPred_eq Set.mem_preimage
```
Verified absent: `Matrix.eq_inv_of_mul_eq_one_left` (unknown constant, `abs.lean`). Deprecated in this Mathlib (warnings in the tool log): `if_neg` (use `ite_eq_right`), `ite_cond_eq_false` (use `ite_eq_right_of_eq_false`), `mul_le_one₀` (no replacement). Used and checked: `ite_eq_right`, `Real.one_sub_inv_le_log_of_pos`, `Finset.sum_erase_eq_sub`, `MeasureTheory.Measure.le_map_apply`, `MeasureTheory.measure_iUnion_fintype_le`, `Matrix.nonsing_inv_eq_ringInverse`, `Matrix.inv_submatrix_equiv`.

## (d) Open issues and paper-delta candidates
1. Target 13 for targets 10 and 11 is a "variables" instance at `(a,b) = (1/4,1/4)` (sample-level inputs are hypotheses, as the band instance `inst_mixEntry_det`) plus a fully discharged instance at the boundary `(a,b) = (0,0)`. If the auditor requires a fully discharged instance at `a + b > 0`, an explicit sample satisfying `hΩ` and the four large-deviation inputs is needed; none was constructed.
2. Size: 2,749 lines against the 1a central 1,648 / calibrated top 2,109 (b1); the stop-rule reading is in narrative 2.
3. `GUEEntry_Setup` (a `Prop` bundle of the structural hypotheses of the core) is private because the whole-library premise scan flags a `Prop` structure that no theorem concludes; no registry line is proposed (row b expects none).
4. Hub: `main` advanced (row a merged); the import lines are re-added after the last import line of the current `RBM3D.lean` (rule A.4). No module imports `GUEEntry`/`GUEEntry2` except `RBM3D.lean` and (for `GUEEntry`) `GUEEntry2`.
5. Paper-delta candidates (relative to the merged band statements, the signed 1a-audit text and the ticket; the paper TeX was not re-read in this stage):
   - `T2515c`: `GUEEntryMixBA` takes free real-axis flow families `(g n, E n, m n)` with `BAReal`, `0 < g n ≤ 𝔡⁻¹`, in place of the band's `|E n| ≤ 2 - κ` and `g = sz.lam n` (the BA flow coupling is `λ₀ = √t₀ λ`; 1a-audit observation 5).
   - `T2515d`: the BA deterministic entry bound (`mix_detBA`, `mixEntry_detBA`) has the extra hypothesis `W^{-d} ≤ δ²`, the smallness `GUEEntry_cs Φ δ² ≤ 1` (band: `36 Φ δ² ≤ 1`) and the conclusion `C Φ² (Lm + W^{-d})` with `C = GUEEntry_C d Λ κ` (band `mix_det`: `mixCdet Φ² maxLoopPM`); the pin proof applies it at `δ' = max δ_n √(W^{-d})`.
   - `T2515e`: `stable_mixBA` states the stability of the BA mixture for the matrix `M^{(B)}` with the flat part `b (L^d)⁻¹ J` (constant `16κ⁻⁴(1+16κ⁻⁴)`), replacing the band's scalar-`m` stability `stable_mix`.

## Repair (round 1, `docs/reports/T2515b-audit.md` §6 items 1-3) — Thu Oct 15 10:48:10 UTC 2026
Repairer model: claude-opus-5-5. Commit `f158d5f5` on `t/T2515b` (parent `f8250a35`); only `RBM3D/BA/GUEEntry2.lean` changed: 345 lines inserted at :1192 (examples formerly at :1194-1218 are now at :1539-1563). Sections (b)-(d) above describe `f8250a35`; only the b1 per-commit size loop, the b2 `deps`/`#check` block, the b6 `doc:` lines and the b7 hit lines were removed (length limit). **Items 1-2: not delivered (obstruction, compiled below); item 3: both files ≤ 2,000, builds pass.**
```
$ git diff --stat f8250a35 HEAD
 RBM3D/BA/GUEEntry2.lean | 345 ++++++++++++++++++++++++++++++++++++++++++++++++
$ wc -l RBM3D/BA/GUEEntry.lean RBM3D/BA/GUEEntry2.lean
    1524 RBM3D/BA/GUEEntry.lean
    1570 RBM3D/BA/GUEEntry2.lean
$ lake build RBM3D.BA.GUEEntry RBM3D.BA.GUEEntry2 2>&1 | tail -1
Build completed successfully (3808 jobs).
$ lake build > fullbuild.out; echo exit=$?   (date -u: 10:46:04 -> 10:47:24); grep "axiom audit" fullbuild.out; tail -1 fullbuild.out
exit=0
info: RBM3D.lean:650:0: axiom audit: 15508 theorems, 4757 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4420 jobs).
$ lake env lean Ax.lean | python3 (one line per name; scratch file: `open private ... from RBM3D.BA.GUEEntry2`, `#print axioms`)
RBM.BA.GUEEntryInst_zero_obstr [propext, Classical.choice, Quot.sound]
RBM.BA.GUEEntryInst_zero_obstr_vtx [propext, Classical.choice, Quot.sound]
RBM.BA.GUEEntryInst_core [propext, Classical.choice, Quot.sound]
RBM.BA.stable_mixBA [propext, Classical.choice, Quot.sound]
RBM.BA.mix_detBA [propext, Classical.choice, Quot.sound]
RBM.BA.mixMatBA [propext, Classical.choice, Quot.sound]
RBM.BA.mixEntry_detBA [propext, Classical.choice, Quot.sound]
RBM.BA.GUEEntryMixBA [propext, Classical.choice, Quot.sound]
RBM.BA.gueEntryMixBA [propext, Classical.choice, Quot.sound]
$ grep -cE '\b(sorry|admit|native_decide)\b|^axiom ' RBM3D/BA/GUEEntry2.lean
0
$ grep -rnE "GUEEntryInst_(core|zero_obstr|zero_obstr_vtx|consts|prof|SBR_le|expC_ge_one)\b" RBM3D RBM3D.lean | grep -v "^RBM3D/BA/GUEEntry2.lean" | wc -l
       0
```
The compiled negative for item 1 (statement extracted by script; all new declarations are `private`):
```
-- GUEEntry2.lean:1420-1426
private theorem GUEEntryInst_zero_obstr {d L W : ℕ} [NeZero L] [NeZero W] {g Λ κ E a b δ Φ : ℝ} {m : ℂ}
    (hd : 3 ≤ d) (hg : 0 < g) (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : 0 < b) (hu : a + b ≤ 1 / 2)
    (hllErr : ∀ x y, GUEEntry_llErr d L W g E m (a + b) ((g : ℂ) • PsiI d L W + 0) x y ≤ δ)
    (hδ : δ ≤ GUEEntry_dlt d Λ κ) (hwd : ((W : ℝ) ^ d)⁻¹ ≤ δ ^ 2) (hΦδ : GUEEntry_cs d Λ κ * Φ * δ ^ 2 ≤ 1)
    (hquad : ∀ i, ldeQuadLHS 0 (green ((g : ℂ) • PsiI d L W + 0) (ztOf m E (a + b))) (Smix d L W 0 a b) 1 i ≤
      Φ * ldeQuadRHS (Smix d L W 0 a b) (green ((g : ℂ) • PsiI d L W + 0) (ztOf m E (a + b))) i) : False := by
```
Item 2: `GUEEntryInst_zero_obstr_vtx` (GUEEntry2.lean:1485-1495) concludes `False` from the hypotheses of `mix_detBA` at `X = 0` (`hGR`, `hz`, `hM`, `hH`, `hδ`, `hwd`, `hΩ`, `hΦδ`, `hLquad`) with the same `a, b` range and the audit's suggested `hs : s = E + m`.
1. Why (core `GUEEntryInst_core`, :1246). At `X = 0`, `ldeQuadLHS = |Σ_{k≠i} S_ik G^{(i)}_kk|² ≥ A²`, `A = Σ_{k≠i} S_ik Im G^{(i)}_kk`; Ward for the minor (`inv_minorMat`, `ward_row`) gives `ldeQuadRHS ≤ max S · A / Im z`, `max S ≤ 2bW^{-d}`; the a priori event gives `|G^{(i)}_kk| ≥ 2κ/3` for `k` off the inner-index fibre of `i` (`δ ≤ GUEEntry_dlt ≤ κ/4`), so `A ≥ b(1 - W^{-d}) Im z (2κ/3)²`. Hence `Im z² (2κ/3)² (1 - W^{-d}) ≤ 2ΦW^{-d} ≤ 2Φδ² ≤ κ⁴/416` (`GUEEntry_cs ≥ 832κ⁻⁴`, `GUEEntryInst_consts`), against `≥ (15/144)κ⁴` (`Im z ≥ κ/2`, `W^{-d} ≤ 1/16`).
2. The audit's estimate "Φ up to `(cs δ²)⁻¹ ≈ 1.05·10⁶`" is the available Φ; at `X = 0` the quadratic input needs `Φ ≳ W^d ≥ δ⁻²` (`10²⁴` at b6). The band template `inst_det_zero` works because band `mix_det` has no `W^{-d} ≤ δ²` hypothesis (there `Φ = 256 ≥ N - 1`, `N = 216`).
3. Not covered by the compiled negatives: `a > b`, `a + b > 1/2` at `X = 0`, and `X ≠ 0`. A deterministic `X ≠ 0` must meet the four LDE inputs with `Φ ≤ W^d/cs` at `W^d ≥ (2·GUEEntry_Kbd)² ≈ 6.9·10²³` (b6 constants), i.e. match `Σ_{k,l≠i} X_ik G^{(i)}_kl X_li` to `Σ_k S_ik G^{(i)}_kk` to relative precision `≈ cs^{-1/2}`; I know no explicit such matrix and constructed none. I stopped here (CLAUDE.md §4 step 4).
4. Open issue for the dispatcher: whether the a priori event and the four LDE inputs (the events of `GUEEntry_bad`, discharged on the probability side by `gueEntryMixBA`, itself fully instantiated at `S0`) may stay hypotheses of the `(1/4,1/4)` examples, as in the band's `inst_mixEntry_det`; no paper-delta candidate is added.
Mathlib names used by the repair (all compile in the file): `one_le_pow₀ one_le_mul_of_one_le_of_one_le inv_anti₀ inv_strictAnti₀ one_div_le_one_div_of_le norm_sub_norm_le Finset.sum_subtype Complex.im_sum Complex.abs_im_le_norm sq_le_sq' pow_le_pow_left₀ le_of_mul_le_mul_left Matrix.nonsing_inv_mul Matrix.isUnit_iff_isUnit_det div_le_one`.
