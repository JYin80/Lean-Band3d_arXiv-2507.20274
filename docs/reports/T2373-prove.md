Prover model: claude-sonnet-5-5
## (a) Math preflight — Sat Oct 10 05:42 UTC 2026 (`date -u` at 05:37:11, 05:40:27, 05:41:50)

Sources read: RBM2D HEAD `9e0f275`; both source files last touched by `81fca44` (comment/dead-code clean-ups T2274/T2276 after `c9a24cf`, the commit `GUELocalBootstrap` was ported from).
`wc -l`: RBM2D `EigenInterlacing` 588, `GUELocalSchur` 570, `Delocalization` 110; RBM3D `GUELocalBootstrap` 1252. The worktree has neither target file yet.

### Design-gate item (i): twin table (RBM2D name -> RBM3D twin; P = public, p = private)
| RBM2D name | RBM3D twin (file:line) | note |
|---|---|---|
| `gueSchurTail` / `GUESchurTail` / `GUELocal_of_tail` / `GUELocal` | `UNGUESchurTail` `GUELocalBootstrap:915` P; `un_gueLocal_of_tail` `:952` P; `UNGUELocal` `Pins:489` P | statement gains `d` (`3 ≤ d`), `sz : Sizes d`, `Nsz sz n`, `gueP d (sz.L n) (sz.W n)` |
| `schurErr`, `schurBud` | `GUELocalBootstrap:185`, `:455` P | same shape |
| `stieltjesN` (green-trace) | `Pins:88` P, **Gres-based** | copy bridge `GUELocalBootstrap_stieltjesN_eq` (`:67`, p): ~12 lines as `GUELocalSchur_*` |
| `Endpoints.gueP`, `Endpoints.gueVar` | `gueP` `Pins:67`, `gueVar` `Pins:61` P | `(W*L)^2` -> `(W*L)^d`; `Measure.infinitePi` unchanged |
| `Xmat L W`, `Idx L W`, `Ω L W`, `card_Idx`, `Xmat_isHermitian` | `Gauss/FineModel:113, :142` P; `Defs/Sizes:46, :107` P (`d L W` explicit), `Sizes.card_Idx` `:160` | `Xmat_diag_eq` copied (4 lines), `simp [Xmat, Xentry]` as in `EntryTail:748` |
| `green` | `Green/EntryCore:34` P | same |
| `Gauss.isUnit_sub_smul_one_of_im_ne_zero` | `RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero` `Induction/ConArgDet:380` P (same `IsUnit` form; used `EntryTail:397`) | rename only |
| `Green.green_diag_paper`, `inv_minor_resolvent`, `minorGreen` | `EntryCore:255`, `:233`, `:59` P | same |
| `Green.green_diag_ne_zero`, `Green.im_green_diag` | `Green/LDE:503`, `:476` P | same |
| `Green.hwConst`, `hwConst_pos` | `Green/IBPPoly:721`, `:723` P | same |
| `gue_quad_tail` | `GUEPhase/AuxCarrier:959` P, `{d L W}` implicit, statement shape identical to RBM2D `AuxCarrier:843` with `^2 -> ^d` | `RBM.Univ`, as RBM2D |
| `gaussianReal_ge_le/le_le/tail`, `gueP_diag_tail` | `EntryTail:706` `mixEntry_gaussianReal_tail` p (not callable) | **copy** (3 Chernoff lemmas + diag tail, ~95 lines, already inside the 570) |
| `RBM.green_eq_spectral` (`Delocalization:47`, only Delocalization name `EigenInterlacing` uses, at `:351`) | `Step1Good:46` p, `InjSum:43` p | **copy** 25 lines as `EigenInterlacing_green_eq_spectral` |
| `green_apply_self`, `im_green_apply_self` | not used by either file (grep) | not copied |
| `EI.*` (24 private lemmas/defs) | none; `grep EI\.\|EigenInterlacing` in RBM3D: 0 hits | rename `EI.x` -> `EigenInterlacing_x` |
| `schur_union_bound`, `final_arith`, `schurErr_eq`, `ward_sum`, `trace_diff_le`, `schur_arith`, `schurErr_le_of_good` | none | **copy**, private, stem `GUELocalSchur_` |
No twin is missing at a cost above 200 lines (largest copy: the Chernoff/diag tail, ~95 lines; already counted).
Registry: `owedProps` lines `Test/Axioms.lean:184` (`UNGUELocal`), `:210` (`UNGUESchurTail`). `scanPremises` (`Test/Axioms.lean:442`) drops a premise some theorem concludes; `gueLocal` concludes `UNGUELocal` and `gueSchurTail` concludes `UNGUESchurTail`, so both lines are to be deleted (T2357 precedent, `83847ef`). Merged theorems that take `UNGUELocal` as hypothesis (e.g. `GUETranslation:56`, `PinsDens:89`, `Step1Band:1007`) are unaffected by that scan logic. The pre-check (target 4) is stage 1b's.

### (i) Exponent table of `gueSchurTail` (`N = (W L)^3 = sz.size n`; `a = N^{ε/2}`, `a² = N^ε` exactly)
| quantity | value / constraint | slack |
|---|---|---|
| `ε, D, κ, τ` | `> 0` free; consumed by `un_gueLocal_of_tail` at `τ=1/10`: `ε = τ'/4 = 1/40`, `D` given, `q = 9`, `Γ = glPts`, `\|Γ\| ≤ N^9` (eventually, `glPts_card`) | - |
| `q'` | `q' = ⌈(q+D+2)/ε⌉`, constraint `q+D+2 ≤ (q'+1)ε` | A (`ε=1/40,D=1,q=9`): `q'=480`, `12 ≤ 12.025`, slack `0.025`; B (`ε=1,D=1,q=0`): `q'=3`, `3 ≤ 4`, slack `1` |
| e1 | `a ≥ 5` iff `N ≥ 5^{2/ε}` | A: `log10 N ≥ 55.92`; B: `a = 1448`, slack `1443` |
| e2 | `N^{q+1+D} e^{-N^ε/2} ≤ 1/4` | A: needs `ln N^ε ≥ 8.98`, i.e. `log10 N ≥ 156.0`; B: `log10 = -455378 ≪ log10(1/4)` |
| e3 | `2 hwConst q' ≤ N`, `hwConst q' = ((2q'+1)(4q'+2))^{q'+1}` | A: `log10 N ≥ 3014.48` (binding); B: `log10(2hw) = 8.266` vs `log10 N = 6.32` at `n=0` |
| e4 | `N ≥ 1` | `N_0 = 2^21` |
| union bound | `\|Γ\| N (2 e^{-a²/2} + hw(q')/(a²)^{q'+1}) ≤ N^{-D}`: each of the two parts `≤ N^{-D}/2` (`final_arith`; part 2 uses `(q'+1)ε ≥ q+D+2` and `hw ≤ N/2`) | B `n=1`: `log10 LHS = -27.26 ≤ -11.74` (slack `15.5`); B `n=0`: `-11.00 ≤ -6.32` holds although e3 fails (e3 is only sufficient) |
| deterministic | `a ≥ 5`: `a²-3a-5 ≥ 0` at `a=5` equals `5`; `π+1 ≤ 5` (`π+1 = 4.1416`, slack `0.858`); `Im m_N ≤ 2` | - |
| diag tail | `Var H_ii = 1/N`, `t = a/√N`: `2e^{-t²N/2} = 2e^{-a²/2}` | exact (n=0, A: both exponents `0.719467`) |
| `∀ᶠ n` | thresholds above; `sz0`: `N_n = 2^21 (n+1)^18`, `N → ∞` (`sz0_tendsto`) | A: `n+1 ≥ 10^167.1`; B: all conditions from `n = 1` |
Honest note: at `n = 0` the eventual conditions e1-e3 fail for the parameters A that `un_gueLocal_of_tail` feeds in (it is a `∀ᶠ n` theorem, so no hypothesis of the target fails; the proof never needs a finite `n`). No exponent fails to close: `q'` is chosen from `(q,D,ε)` with slack `≥ 0`.
Command: `cd .../scratchpad/T2373 && python3 -I exp_table.py | awk '/B n= 2/{exit} {print}' | grep -v "   N :\|q_prime :\|^N_n\|^== Row"` (`n=0` of `sz0` is `N=2097152=2^21`):
```
A n= 0
   q+D+2 <= (q+1)eps : (12, 12.025)
   e1: a=N^(eps/2) >= 5 : (1.199555576040902, False)
   e2: log10(N^(q+1+D)exp(-N^eps/2)) vs log10(1/4) : (69.22546854156765, False)
   e3: log10(2 hw(q')) vs log10 N : (3014.4763568471794, 6.3216299089436045, False)
   final: log10(LHS) vs log10(N^-D) : (3001.3740262859046, -6.3216299089436045, False)
  A thresholds: q_prime= 480
  e1 needs log10 N >= 55.91760034688151
  e3 needs log10 N >= 3014.4763568471794
  e2 needs ln Y >= 8.979999999999853  i.e. log10 N >= 155.99857789964548
  binding log10 N >= 3014.4763568471794  => sz0 index n+1 >= 10^167.1
B n= 0
   q+D+2 <= (q+1)eps : (3, 4.0)
   e1: a=N^(eps/2) >= 5 : (1448.1546878700494, True)
   e2: log10(N^(q+1+D)exp(-N^eps/2)) vs log10(1/4) : (-455378.12739636627, True)
   e3: log10(2 hw(q')) vs log10 N : (8.26593429843396, 6.3216299089436045, False)
   final: log10(LHS) vs log10(N^-D) : (-10.999985424060833, -6.3216299089436045, True)
B n= 1
   q+D+2 <= (q+1)eps : (3, 4.0)
   e1: a=N^(eps/2) >= 5 : (741455.2001894653, True)
   e2: log10(N^(q+1+D)exp(-N^eps/2)) vs log10(1/4) : (-119377958159.4144, True)
   e3: log10(2 hw(q')) vs log10 N : (8.26593429843396, 11.740169830895265, True)
   final: log10(LHS) vs log10(N^-D) : (-27.25560518991582, -11.740169830895265, True)
```

### (ii) Concrete nondegenerate instance (target 3 data), `python3 -I instance.py`
```
eig A = [0.5857864376269049, 2.0, 3.414213562373095]  gaps: [1.4142135623730951, 1.414213562373095]
eig minor = [1.0, 3.0]
i=0: lam_i<=mu_i True ; mu_i<=lam_{i+r} True
i=1: lam_i<=mu_i True ; mu_i<=lam_{i+r} True
|tr G_A - tr G_B| = 0.521812 <= 4.141593 : True
hyp: |H_ii|=1.000<=2.887 True; hquad 0.27778<=4.16667 True; Im m=0.6667<=2 True; a>=5 True
|schurErr| = 1.201850 <= bud 43.179505 : True
ward: eta*S = 1.500000 vs Im tr G^(i) = 1.500000
trace diff = 0.707107 <= (pi+1)/eta = 4.141593
sz0 n=0: N= 2097152 =2^21: True
schurBud N eps I = 0.00239953  N^eps=1.438934
window: |Re z|=0<=2-kappa=1 ; N^(-1+tau)=2.044e-06<=Im z=1<=10 ; card 1<=N^q=7.846e+56
diag tail exponent t^2 N/2 = 0.719467 ; a^2/2 = 0.719467
```
- Interlacing: `A = tridiag(1,2,1)` (3x3 Hermitian, distinct eigenvalues `2-√2, 2, 2+√2`), minor `[[2,1],[1,2]]` (delete row/col 0, `e = succ : Fin 2 ↪ Fin 3`), `z = 0.3+i`; the Lean `example` applies `eigenvalues₀_submatrix_interlace` (`i = 0, 1`) and `trace_green_submatrix_sub_le` (`r = 1`) with `hA` discharged by entries. Eigenvalues are not computable by `norm_num`, so the example's conclusion stays symbolic in `eigenvalues₀` (hypotheses concrete); the numbers above are the script check.
- Schur lemma: `H = diag(1,0,-1)` (3x3, `M = 3`), `i = 0`, `z = i`, `a = 5` (`H_ik = 0`, so `Q_i = 0`); all five hypotheses of `schurErr_le_of_good` hold; the conclusion `‖schurErr‖ = 1.2019 ≤ 43.18`. Also `schur_arith`, `trace_diff_le`, `ward_sum` at the same data (the Ward identity is exact: `1.5 = 1.5`).
- `gueSchurTail` hypotheses at `d = 3`, `sz0` (`sz0_tendsto`), `κ = 1, τ = 1/10, ε = 1/40, D = 1, q = 9`, `Γ n = {I}`: window, card and `Tendsto` all hold; `schurBud N ε I = 0.0024` at `n = 0`. The `gueSchurTail` conclusion is `∀ᶠ`, so the example applies it with hypotheses discharged and does not evaluate a finite `n`.
- External hypothesis: none (`UNGUESchurTail`, `UNGUELocal` are proved, no limit check owed).

### Design-gate item (iv): plan against the stop line 1700 (ticket estimate 1000 / 1250 / 1550)
Arithmetic from the `wc -l` above (RBM2D lines plus additions; `EI.` -> `EigenInterlacing_` renames lengthen lines, so `set_option linter.style.longLine false` is added, 1 line):
| section | file | lines (central) |
|---|---|---|
| 1 header, imports, Abstract (RBM2D `:1-131`) | EigenInterlacing | ~131 |
| 2 Matrices, Push, `eigenvalues₀_submatrix_interlace` (`:133-337`) | EigenInterlacing | ~205 |
| 3 Trace, TraceMain, `trace_green_submatrix_sub_le` (`:339-588`) + copied `green_eq_spectral` (25) | EigenInterlacing | ~275 |
| 4 instance (3x3 and minor) | EigenInterlacing | ~40 |
| **EigenInterlacing total** (+1 `set_option` line) | | **~652**; commit after it builds |
| 5 header (`:1-61`), Det (`:62-238`) + Gres bridge (12) | GUELocalSchur | ~250 |
| 6 DiagTail (`:242-337`), Union (`:341-429`), Constants (`:433-502`), `d`-edits (8) | GUELocalSchur | ~263 |
| 7 Main (`:506-570`) | GUELocalSchur | ~65 |
| 8 instances (`schurErr_le_of_good` at `diag(1,0,-1)`, `schurBud` at `sz0`, `n=0`; `gueSchurTail`/`gueLocal` applied) | GUELocalSchur | ~90 |
| **GUELocalSchur total** (`570 + 12 + 8 + 90`) | | **~668** |
| **both files** | | **~1320** (+12% for line wraps: ~1480) |
Central `1320 ≤ 1500`, with wraps `1480 < 1700`: the split rule does not trigger. Commit points: after section 4 (`wc -l` of the two files), then after 5, 6, 8. Risks (no extra lines expected): (1) `stieltjesN` is Gres-based, bridged in the two uses (`schurErr_eq`, `schurErr_le_of_good`: replace `unfold stieltjesN` by the bridge); (2) in `gueSchurTail` the equality `Nsz sz n = ((W*L)^d : ℕ)` is `Sizes.size` unfolding (defeq, as in RBM2D with `d.size n`); (3) `gue_quad_tail` takes `{d L W}` implicit, `Xmat_isHermitian` and `Xmat_diag_eq` take `d L W` explicit.

### Verdicts
- Target 1 `RBM3D/Universality/EigenInterlacing.lean` (`eigenvalues₀_submatrix_interlace`, `trace_green_submatrix_sub_le`): PASS. Generic in `n, m`; one copy (25 lines); instance data above.
- Target 2 `RBM3D/Universality/GUELocalSchur.lean` (`gueSchurTail`, `gueLocal`): PASS. Exponent `q'` closes with slack `≥ 0`, all twins present, hypotheses satisfiable at the instance.
- Target 3 instances: PASS (nonvacuous data above). Target 4 registry: delete both lines; pre-check deferred to stage 1b.

## (b) Script output — Sat Oct 10 06:23:56 UTC 2026 (`date -u`; worktree `RBM3D-wt/T2373`, branch `t/T2373`; long checks ran 06:12:47–06:21:19 UTC)
```
$ TZ=UTC git log --format="%h %cd %s" --date=format-local:"%H:%M:%S UTC" c0a7747..t/T2373 | cut -c1-100
4aa6933 06:11:46 UTC T2373: instance docstrings, explicit imports of Pins and Step1RegularityGUE
31553ce 06:07:27 UTC T2373: GUELocalSchur port (gueSchurTail, gueLocal) with instances; registry: de
cc5a7e8 05:48:41 UTC T2373: EigenInterlacing port (Cauchy interlacing, trace_green_submatrix_sub_le)
$ git diff --stat main...t/T2373
 RBM3D/Test/Axioms.lean                   |   2 -
 RBM3D/Universality/EigenInterlacing.lean | 702 ++++++++++++++++++++++++++
 RBM3D/Universality/GUELocalSchur.lean    | 823 +++++++++++++++++++++++++++++++
 3 files changed, 1525 insertions(+), 2 deletions(-)
$ wc -l RBM3D/Universality/EigenInterlacing.lean RBM3D/Universality/GUELocalSchur.lean   # stop line 1700 (both files)
     702 RBM3D/Universality/EigenInterlacing.lean
     823 RBM3D/Universality/GUELocalSchur.lean
    1525 total
$ lake build RBM3D.Universality.EigenInterlacing RBM3D.Universality.GUELocalSchur 2>&1 | tail -1
Build completed successfully (3375 jobs).
$ lake env lean RBM3D/Universality/EigenInterlacing.lean; echo exit=$?     # fresh compile: every warning would print
exit=0
$ lake env lean RBM3D/Universality/GUELocalSchur.lean; echo exit=$?
exit=0
$ lake env lean /Users/junyin/Lean_proof/RBM3D/docs/tickets/checks/T2373-check.lean > o_check.txt; echo exit=$?; grep -c error o_check.txt
exit=0
0
$ lake env lean ax_gs.lean   # #print axioms of 20 new public declarations, then the two auditor examples
'RBM.Univ.gueSchurTail' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.gueLocal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.eigenvalues₀_submatrix_interlace' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.trace_green_submatrix_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" o_axioms.txt; tail -1 o_axioms.txt
20
exit=0
  ax_gs.lean: example : RBM.Univ.UNGUESchurTail := RBM.Univ.gueSchurTail
  ax_gs.lean: example : RBM.Univ.UNGUELocal := RBM.Univ.gueLocal
$ grep -n "sorry\|admit\|native_decide\|axiom" RBM3D/Universality/EigenInterlacing.lean RBM3D/Universality/GUELocalSchur.lean | wc -l
0
$ awk '/^theorem (eigenvalues₀_submatrix_interlace|trace_green_submatrix_sub_le)/{p=1} p{print} p&&/:= by$/{p=0}' RBM3D/Universality/EigenInterlacing.lean
theorem eigenvalues₀_submatrix_interlace {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) (e : m ↪ n)
    (i : ℕ) (hi : i < Fintype.card m) :
    (hA.submatrix e).eigenvalues₀ ⟨i, hi⟩ ≤
        hA.eigenvalues₀ ⟨i, hi.trans_le (Fintype.card_le_of_embedding e)⟩ ∧
      hA.eigenvalues₀ ⟨i + (Fintype.card n - Fintype.card m), by
          have := Fintype.card_le_of_embedding e; omega⟩ ≤
        (hA.submatrix e).eigenvalues₀ ⟨i, hi⟩ := by
theorem trace_green_submatrix_sub_le {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) (e : m ↪ n)
    {z : ℂ} (hz : 0 < z.im) :
    ‖(RBM.green A z).trace - (RBM.green (A.submatrix e e) z).trace‖ ≤
      ((Fintype.card n - Fintype.card m : ℕ) : ℝ) * (Real.pi + 1) / z.im := by
$ grep -n '^theorem gue\(SchurTail\|Local\)' RBM3D/Universality/GUELocalSchur.lean   # the types are the merged pins (GUELocalBootstrap.lean:915, Pins.lean:489), untouched by the branch
540:theorem gueSchurTail : UNGUESchurTail := by
591:theorem gueLocal : UNGUELocal := un_gueLocal_of_tail gueSchurTail
$ sed -n '678,699p' RBM3D/Universality/EigenInterlacing.lean | <drop docstrings, blank lines>   # instances of the two interlacing targets
example :
    ((A3_isHermitian.submatrix (Fin.succEmb 2)).eigenvalues₀ ⟨0, by simp⟩ ≤
        A3_isHermitian.eigenvalues₀ ⟨0, by simp⟩ ∧
      A3_isHermitian.eigenvalues₀ ⟨1, by simp⟩ ≤
        (A3_isHermitian.submatrix (Fin.succEmb 2)).eigenvalues₀ ⟨0, by simp⟩) ∧
    ((A3_isHermitian.submatrix (Fin.succEmb 2)).eigenvalues₀ ⟨1, by simp⟩ ≤
        A3_isHermitian.eigenvalues₀ ⟨1, by simp⟩ ∧
      A3_isHermitian.eigenvalues₀ ⟨2, by simp⟩ ≤
        (A3_isHermitian.submatrix (Fin.succEmb 2)).eigenvalues₀ ⟨1, by simp⟩) :=
  ⟨eigenvalues₀_submatrix_interlace A3_isHermitian (Fin.succEmb 2) 0 (by simp),
    eigenvalues₀_submatrix_interlace A3_isHermitian (Fin.succEmb 2) 1 (by simp)⟩
example :
    ‖(RBM.green A3 ((3 / 10 : ℂ) + Complex.I)).trace -
        (RBM.green (A3.submatrix (Fin.succEmb 2) (Fin.succEmb 2))
          ((3 / 10 : ℂ) + Complex.I)).trace‖ ≤ Real.pi + 1 := by
  have h := trace_green_submatrix_sub_le A3_isHermitian (Fin.succEmb 2)
    (z := (3 / 10 : ℂ) + Complex.I) (by simp)
  simpa using h
$ sed -n '708,714p;738,740p;793,820p' RBM3D/Universality/GUELocalSchur.lean | <drop docstrings, blank lines>   # schurErr_le_of_good, schurBud, gueSchurTail, gueLocal
example : ‖schurErr H3 Complex.I 0‖ ≤ 5 ^ 2 * (1 / Real.sqrt ((3 : ℕ) : ℝ) +
    Real.sqrt (2 / (((3 : ℕ) : ℝ) * Complex.I.im)) + 1 / (((3 : ℕ) : ℝ) * Complex.I.im)) :=
  GUELocalSchur_schurErr_le_of_good H3_isHermitian (by simp) 0 (M := 3) (by simp) (a := 5)
    (by norm_num) H3_hmim H3_hdiag H3_hquad
theorem schurBud_sz0_zero :
    0 < schurBud (Nsz sz0 0) (1 / 40) Complex.I ∧
      schurBud (Nsz sz0 0) (1 / 40) Complex.I ≤ 1 / 100 := by
example : ∀ᶠ n in atTop, gueP 3 (sz0.L n) (sz0.W n)
      {ω | ∃ z ∈ ({Complex.I} : Finset ℂ), ∃ i : Idx 3 (sz0.L n) (sz0.W n),
        (stieltjesN (Xmat 3 (sz0.L n) (sz0.W n) ω) z).im ≤ 2 ∧
          schurBud (Nsz sz0 n) (1 / 40) z <
            ‖schurErr (Xmat 3 (sz0.L n) (sz0.W n) ω) z i‖} ≤
      ENNReal.ofReal (Nsz sz0 n ^ (-(1 : ℝ))) :=
  gueSchurTail 3 le_rfl sz0 Step1RegularityGUEInst.inst_sz0_size_tendsto 1 (1 / 10) (1 / 40) 1
    one_pos (by norm_num) (by norm_num) one_pos 9 (fun _ => {Complex.I})
    (fun n z hz => by
      rw [Finset.mem_singleton.1 hz]
      refine ⟨by simp, ?_, by simp⟩
      simpa using Real.rpow_le_one_of_one_le_of_nonpos (one_le_Nsz n) (by norm_num))
    (Filter.Eventually.of_forall fun n => by
      simpa using one_le_pow₀ (one_le_Nsz n) (n := 9))
example : ∀ᶠ n in atTop, gueP 3 (sz0.L n) (sz0.W n)
      {ω | ∃ z : ℂ, |z.re| ≤ 2 - 1 ∧ Nsz sz0 n ^ (-1 + 1 / 10 : ℝ) ≤ z.im ∧ z.im ≤ 10 ∧
          Nsz sz0 n ^ (1 / 10 : ℝ) / Real.sqrt (Nsz sz0 n * z.im) <
            ‖stieltjesN (Xmat 3 (sz0.L n) (sz0.W n) ω) z - msc z‖} ≤
      ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) :=
  gueLocal 3 le_rfl sz0 Step1RegularityGUEInst.inst_sz0_size_tendsto 1 (1 / 10) 2 one_pos
    (by norm_num) (by norm_num)
$ git grep -n -w -e gueSchurTail -e gueLocal -e eigenvalues₀_submatrix_interlace -e trace_green_submatrix_sub_le main -- RBM3D RBM3D.lean | cut -c1-100
main:RBM3D/Main/BUnivHolds.lean:33:  `gueSchurTail`, `gueLocal`).
$ git grep -n -e EigenInterlacing_ -e GUELocalSchur_ -e EigenInterlacingInst -e GUELocalSchurInst main -- RBM3D RBM3D.lean | wc -l
0
$ cat precheck.lean; lake env lean precheck.lean > precheck.out; echo exit=$?; head -1 precheck.out | cut -c1-96; grep -c "UNGUELocal\|UNGUESchurTail" precheck.out
import RBM3D
import RBM3D.Universality.GUELocalSchur
#assert_rbm_axioms
exit=0
axiom audit: 10855 theorems, 3188 definitions, 0 axioms in `RBM` (compiler-generated declaration
0
$ git diff main...t/T2373 -- RBM3D/Test/Axioms.lean | grep "^[-+]   " | cut -c1-84
-   `RBM.Univ.UNGUELocal, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01:
-   `RBM.Univ.UNGUESchurTail, -- bulk universality pin, the Schur tail of the GUE lo
$ lake build     # RBM3D.lean as committed: no root import of the two new modules
error: RBM3D.lean:415:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedPr
  [RBM.Univ.UNGUESchurTail]
exit=1
$ lake build     # + temporary uncommitted imports of the two modules after the last import line, restored by cp
Build completed successfully (4185 jobs).
exit=0
$ git status --short | wc -l; diff RBM3D.lean $S/RBM3D.lean.orig && echo restored
0
restored
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks log -1 --format=%h; ... diff --stat 81fca44 HEAD -- RBM2D/Universality/EigenInterlacing.lean RBM2D/Universality/GUELocalSchur.lean RBM2D/Delocalization.lean | wc -l
9e0f275
0
$ diff <(sed -n 27,586p $R/EigenInterlacing.lean | sed "s/EI\./EigenInterlacing_/g") <(sed -n 36,628p RBM3D/Universality/EigenInterlacing.lean) | ...;  likewise GUELocalSchur 62,502 vs 75,530
EigenInterlacing: hunks 3, removed 2, added 35
GUELocalSchur: hunks 50, removed 86, added 101
```

**Narrative** (facts as in the script output above; line numbers of the committed files; all scratch files in `scratchpad/T2373/`).
- `EigenInterlacing.lean` (702 lines): `:36-628` is the port of RBM2D `:27-586`; the diff has 3 hunks: `push_neg` -> `push Not` (the build log at 05:44 UTC warned `push_neg` is deprecated), the one inserted private lemma `EigenInterlacing_green_eq_spectral` (`:354`, copy of `RBM2D/Delocalization.lean:47`), and its use (`:393`); `EI.x` -> `EigenInterlacing_x`; instances `:630-700`.
- `GUELocalSchur.lean` (823 lines): `:75-266` `Det` (16 inserted lines: the `Gres` bridge `GUELocalSchur_Gres_true`, `GUELocalSchur_stieltjesN_eq`), `:268-365` diagonal tail, `:367-457` union bound, `:459-530` constants, `:532-593` `gueSchurTail`, `gueLocal`, `:595-821` instances.
- Changes against RBM2D (50 hunks, script output): private helpers carry the stem; `Idx`, `Ω`, `Xmat`, `gueP`, `gueVar` take `d`; `(W * L) ^ 2` -> `(W * L) ^ d`; `card_Idx L W` -> `RBM.Gauss.card_Idx d L W` (the bare name is ambiguous with `Sizes.card_Idx`: build error "Ambiguous term" at 05:50 UTC); `unfold schurErr stieltjesN` -> `unfold schurErr; rw [GUELocalSchur_stieltjesN_eq]` in `schurErr_eq` and `schurErr_le_of_good` (`stieltjesN` is `Gres`-based); `RBM.Gauss.isUnit_sub_smul_one_of_im_ne_zero` -> `RBM.isUnit_sub_smul_of_isHermitian` (`Analysis/Resolvent.lean:132`; same `IsUnit (H - z • 1)` shape; (a) line 16 named `RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero`, equally public); `((d.size n : ℕ) : ℝ)` -> `Nsz sz n`.
- `gueSchurTail` has the type of the pin `UNGUESchurTail`; its proof is RBM2D `:515-562` (`q' = ⌈(q+D+2)/ε⌉₊`, `a = N^{ε/2}`, `e1`-`e4` of (a)(i), `schur_union_bound`, `final_arith`).  It uses none of `3 ≤ d`, `0 < κ`, `0 < τ`, `0 < D`: a scratch copy with those four `intro` names replaced by `_` compiles (no output).
- The Gaussian tails `GUELocalSchur_gaussianReal_ge_le/le_le/tail` are copies of `EntryTail.lean:690-740` (private there); `GUELocalSchur_gueP_diag_tail` is RBM2D's with `d`; `gue_quad_tail` (`AuxCarrier.lean:959`) is called with `lam = a ^ 2`.
- Instances, interlacing: `A3 = tridiag(1,2,1)`, minor `[[2,1],[1,2]]` (`Fin.succEmb 2`); `A3_eigenpairs` checks three eigenpairs of `A3` with distinct eigenvalues `2+√2, 2, 2-√2` and two of the minor; the interlacing conclusion stays symbolic (spectrum not evaluated), the trace corollary is numeric (`≤ π + 1` at `z = 3/10 + i`).
- Instances, Schur: `H3 = diag(1,0,-1)`, `i = 0`, `z = i`, `a = 5`: `H3_Q` (`Q_0 = 0`), `H3_trace` (`tr G⁽⁰⁾ = (-1+3i)/2`), `H3_hquad` (Ward identity of the minor gives `∑∑|G⁽⁰⁾|² = 3/2`), `H3_hmim` (`norm_stieltjesN_le`), `H3_hdiag`; `schurErr_eq`, `trace_diff_le`, `ward_sum` at the same data (`:717-725`); the Gaussian, diagonal and union-bound lemmas at concrete data (`:764-768`); `schurBud_sz0_zero`; `final_arith` at `q = 0, D = ε = 1, q' = 2, N = 10^10` (`:771-789`); `gueSchurTail` (`D = 1`) and `gueLocal` (`D = 2`) at `sz0`.
- Registry: both `owedProps` lines deleted.  `UNGUELocal` was already outside the scan's `found` set (`scanPremises` counts `un_gueLocal_of_tail`, whose conclusion is `UNGUELocal`, as proving it): the as-committed build flags only `UNGUESchurTail`.  The pre-check passes (exit 0, no mention of either name).  The branch's own full `lake build` fails by design until the hub adds the root imports; with them it passes.
- Stop rule: `wc -l` of the two files before the three commits printed 702 (05:48), 1522 (06:07), 1525 (06:11); stop line 1700.  No pin, signature or hypothesis changed; no external input; no `sorry`, `axiom`, `native_decide`; helpers private with the stems.

## (c) Verified Mathlib names (script `names.lean`: each name resolved under the file's `open`s; 36 `ok`, 2 `ABSENT`; output of `lake env lean names.lean`)
Matrix.isHermitian_diagonal_iff Matrix.submatrix_diagonal Matrix.inv_eq_right_inv Matrix.diagonal_mul_diagonal Matrix.diagonal_one
Matrix.diagonal_apply Matrix.diagonal_apply_ne Matrix.IsHermitian.eigenvalues₀ Matrix.IsHermitian.submatrix Fin.succEmb
Fin.sum_univ_three Real.pow_div_factorial_le_exp Real.rpow_le_one_of_one_le_of_nonpos one_le_pow₀ Complex.abs_im_le_norm
Real.le_sqrt_of_sq_le Real.sqrt_le_iff inv_eq_of_mul_eq_one_right Finset.mem_singleton Finset.card_singleton
ProbabilityTheory.measure_ge_le_exp_mul_mgf ProbabilityTheory.measure_le_le_exp_mul_mgf ProbabilityTheory.mgf_id_gaussianReal ProbabilityTheory.integrable_exp_mul_gaussianReal MeasureTheory.Measure.infinitePi_map_eval
MeasureTheory.measure_biUnion_finset_le MeasureTheory.measure_iUnion_fintype_le tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero tendsto_rpow_atTop tendsto_natCast_atTop_atTop
LinearMap.IsSymmetric.eigenvalues_antitone Matrix.toEuclideanLin_conjTranspose_eq_adjoint intervalIntegral.integral_eq_sub_of_hasDerivAt Matrix.IsHermitian.spectral_theorem Matrix.trace_mul_cycle
Finset.sum_range_add
ABSENT: `Matrix.charpoly_fin_three` (only `Matrix.charpoly_fin_two`, `Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean:229`), `Matrix.IsHermitian.eigenvalues_diagonal`.  Signature note: `Real.pow_div_factorial_le_exp (x : ℝ) (hx : 0 ≤ x) (n : ℕ)` takes `x` explicitly (compile error at 06:01 UTC).  Deprecated in this Mathlib (build logs): `push_neg` (use `push Not`), `if_true` (use `ite_true`).

## (d) Open issues and paper-delta candidates
- `Test/Axioms.lean:183` (the `UNBUniv` line, T2371's) still calls `UNGUESchurTail` owed (producer T2373): stale after this merge; outside this ticket's lines, not edited.
- `gueSchurTail` does not use `3 ≤ d`, `0 < κ`, `0 < τ`, `0 < D` (narrative); the pin is unchanged.  The interlacing instance leaves the spectrum symbolic (no `charpoly_fin_three` in Mathlib).
- Paper-delta candidate `T2373a`: no new statement difference.  `UNGUELocal` and its input `UNGUESchurTail` are project-internal (not in the paper: the RBM2D paper `1_2:566-581` cites only `MR:locSC` and [32]; paper-delta T2162b) and are now proved for every `d` by the Schur identity, the diagonal Gaussian tail, `gue_quad_tail` (Hanson-Wright) and Cauchy interlacing; propose marking T2162b as proved by T2373.
