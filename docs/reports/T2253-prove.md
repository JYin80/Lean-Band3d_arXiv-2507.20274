Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 04:47:18 UTC 2026

### (i) Exponent table

Targets are deterministic identities/inequalities on one finite matrix; no `N`-power exponent, no `L`-`W` relation, no `3 <= d` hypothesis (`d` enters only via `Idx d L W` and `centeredVarianceEntry d L W lam`; `N = card (Idx d L W) = (W L)^d`, `Defs/Sizes.lean:107`). Rows:

| quantity | value | constraint | slack |
|---|---|---|---|
| `d, L, W` | any, `NeZero L`, `NeZero W` (instance `d=3, L=3, W=2`) | `Idx` nonempty, `N>=1` | `N = 6^3 = 216` |
| `lam` | any real (instance `1/2`) | kernel weights `a=(1+2d lam^2)^-1`, `b=lam^2 a` need `1+2d lam^2>0` | all real `lam`; at `lam=1/2`, `d=3`: `a=0.4`, `b=0.1`, `a+2d b=1` |
| row sum of `S=svarF` | `1` (script: min=max=1.0) | `S° = S - N^-1` has row sums 0 | script: `max abs = 1.7e-16`; so `K1=0` at scalar `H` (non-scalar `diagH` needed for a nontrivial instance) |
| symmetry `S°_ab = S°_ba` | exact (`svarF_comm`) | used for index swaps in targets 1-3 | script: `sym = 0.0` |
| `1/N`, `1/N^2` in `K1`, `K2` | `N^-1`, `N^-1*N^-1` (`L2t` writes `(N^-1)^2`) | equal | exact (`paperL2Kernel_eq_L2t` is `sq`) |
| target 1 | `sum S° wirtSecond(Im m) = 2 Im K1(z;+,+)` | `H` Hermitian, `Im z != 0` | identity (rel err <= 1.2e-12 in script) |
| target 2 | `sum S° d Im m(z1) d Im m(z2) = -1/4 (K2++ - K2+- - K2-+ + K2--)` | `H` Hermitian, `Im z_i != 0` | identity (rel err <= 1.7e-15); signs `+,-,-,+`, constant `-1/4` as in the script |
| target 3 Leibniz counts | `|s|` single terms plus `|s|(|s|-1)` ordered pairs `(i,j)`, `j in s.erase i`; rest-product over `(s.erase i).erase j` | `Im z_i != 0` | identity (rel err <= 5.5e-12; also with `Im z1<0`: 1.4e-13) |
| target 4a `conj K1++ = K1--` | conj of `(G^2)_aa` is `(G*^2)_aa` (needs `H` Hermitian); `S°`, `N^-1` real | `H` Hermitian | script `conj check <= 2.7e-18` |
| target 4b `|2 Im K1| <= L1` | `|2 Im K1| <= |K1++|+|K1--|`; `L1` is the 4-term sum over signs | 4a | `0.1286 <= 3.534` (diagH, z=0.3+0.5i) |
| target 4c `|-1/4 (...)| <= L2` | `1/4 sum |K2| <= sum |K2|` | none (no Hermitian hypothesis) | factor 4 in the coefficient |
| target 4d/5 positivity | `prod_j Im m(z_j) >= 0` | `H` Hermitian, `Im z_j > 0` (`stieltjesN_im_eq_normalized_specWeight`, `InjSum.lean:196`: `Im m = N^-1 sum eta/((l-E)^2+eta^2)`) | strict `Im z > 0`; targets 1-3 need only `Im z != 0` |
| target 4d/5 bound | `\|Hessian contraction\| <= sum_i prod_{j!=i} Im m_j * L1 + sum_{i!=j} prod_rest * L2` | as above | script ratios `\|LHS\|/(L1+L2)`: 0.1016, 0.1068, 0.3486, 0.2000 (all < 1) |
| consumer `UNEMCTE2` (`Pins.lean:669-681`) | `s = Finset.univ : Finset (Fin nf)`, `lam = sz.lam n`, `H = ouMat (UNModel.band sz) n s ω`; `UNEMCTE2k` (`PinsK.lean:345-356`): `lam = K.lamV sz n` | statements `lam`-generic | see below |

Consumer token check (`docs/tickets/checks/T2253-check.lean` last `example`; `Pins.lean:675-676, 680-681`): the pin's integrands are `(∏ j ∈ Finset.univ.erase u, (stieltjesN (ouMat …) (z j)).im) * L1t d (sz.L n) (sz.W n) (sz.lam n) (ouMat …) (z u)` and `(∏ k ∈ (Finset.univ.erase u).erase v, …) * L2t … (z u) (z v)`; they are the summands `∏ j ∈ s.erase i, … * L1t d L W lam H (z i)` and `∏ k ∈ (s.erase i).erase j, … * L2t … (z i) (z j)` of target 5 at `s = univ`. UN-18 sums `nf` single terms and `nf(nf-1)` ordered pairs `(u,v)`, `u != v` (the pin bounds all `u ≠ v`). `ouMat_isHermitian` (`Pins.lean:154`) gives `hH` for every `t, ω`. `InWindow` (`Pins.lean:501`) gives `Nsz^(-1-τU) <= z.im`, and `Nsz sz n = ((W n * L n)^d : ℕ) >= 1` (`Defs/Sizes.lean:157`, `W_pos`, `three_le_L`), so `0 < Nsz^(-1-τU) <= z.im`.
`lam` threading: every `centeredVarianceEntry`, `paperK*Contraction`, `paperL*Kernel` gets the same free real `lam`; the only symmetry used is `centeredVarianceEntry_symm d L W lam` (`OUHessian.lean:1138`).

### (ii) Concrete nondegenerate instance

`d=3, L=3, W=2` (`N=216`), `lam=1/2`, `ι = Fin 2`, `s = univ`, `z = (I, 2I)`, `H = diagH = diagonal(k ↦ val(k 0)/3)` on `Idx 3 3 2 = (ZMod 6)^3` (values `0, 1/3, ..., 5/3`; real diagonal hence Hermitian; non-scalar: `x0 = 0 ↦ 0`, `x1 = Pi.single 0 1 ↦ 1/3`); also `H = 1`. Hypotheses: `H.IsHermitian` (script: `max|H-H^*| = 0.0`), `Im z = 1, 2 > 0`, `NeZero 3`, `NeZero 2`. No empty index, no `N=0`, no collapsed window. Nontriviality: `2 Im K1(diagH, z=I; +,+) = -0.1301`, while at `H=1`, `2 Im K1 = -2.5e-16` (zero: row sums of `S°` vanish; at `H=1` both sides of target 1 are round-off zeros, so the pasted relative error 8e-3 is `-2.45e-16` vs `-2.47e-16`).
The Hessian is computed from the definition `wirtSecond` (`Bmat` directions `E_ij+E_ji`, `iE_ij - iE_ji`; `1/4 (D_real^2 + D_imag^2)` off the diagonal, `D^2` along `E_ii` on it) with `f'' = Im(2 N^-1 tr(A G A G^2))`, validated by central finite differences (FD lines: rel <= 1.4e-6 in the pasted lines, <= 7.6e-6 over all 12 coordinate checks of the script); `S°` built from `svarF = W^-d * sbKernelR(block(i)-block(j))` with block `= val(k)/W mod L` and `|.|` the periodic `l1` distance (`Defs/Lattice.lean:25, 71`, `Defs/Block.lean:74`, `Gauss/FineModel.lean:47`). Targets 1-3 are tested at `diagH`, a random Hermitian `H` (`N=216`, seed 1), `diagH` at `z=(I,2I)`, `H=1`; `target5` lines test targets 4d/5 (there `L1`, `L2` are sums of `paperL1Kernel`, `paperL2Kernel`, equal to `L1t`, `L2t` by `paperL1Kernel_eq_L1t`, `paperL2Kernel_eq_L2t`, `OUHessian.lean:1150, 1157`).

Command (Python, scratchpad `T2253/pf.py`, `pf_neg.py`; no Lean) and verbatim output (filter: `grep -E "S row|S° row|target|i=0 K1|\(5, 70, True\)"`; for `pf_neg.py`: `grep -E "target[123]"`):
```
$ python3 pf.py | grep -E "S row|S° row|target|i=0 K1|\(5, 70, True\)"; python3 pf_neg.py | grep -E "target[123]"
S row sums min/max 1.0 1.0 sym 0.0 N 216
S° row sums max abs 1.6653345369377348e-16 S° min entry -0.004629629629629629
diagH FD vs analytic D2 (5, 70, True) -0.05697293508007241 -0.056972854878267754 rel 1.407717621413125e-06
diagH i=0 K1(+,+)= (0.7640912851253825-0.0642864791466638j) 2Im K1= -0.1285729582933276 |.|<=L1: 0.1285729582933276 <= 3.5336855161384997 conj check 0.0
diagH target3: LHS -0.23642453630820287 RHS (-0.2364245363083366+1.6940658945086007e-21j) rel err 5.6561964931497e-13
diagH target5: |LHS|=2.364245e-01 <= L1+L2 = 2.326502e+00 ; slack ratio 0.1016
diagH target1: LHS -0.12857295829347504 RHS 2Im K1 -0.1285729582933276 rel err 1.1467233827947405e-12
diagH target2: LHS (5.194863934770423e-05+0j) RHS (5.194863934770432e-05+1.6940658945086007e-21j) rel err 1.6960543184609993e-15
randH FD vs analytic D2 (5, 70, True) -0.0045966144928559815 -0.004596612535046063 rel 4.259243235576459e-07
randH i=0 K1(+,+)= (-0.00015652656309570097+6.0874824718403053e-05j) 2Im K1= 0.00012174964943680611 |.|<=L1: 0.00012174964943680611 <= 0.0008915120211589464 conj check 2.646215520710063e-18
randH target3: LHS 9.755295626348028e-05 RHS (9.755295626346555e-05+3.917527381051139e-21j) rel err 1.5101128765125446e-13
randH target5: |LHS|=9.755296e-05 <= L1+L2 = 9.130312e-04 ; slack ratio 0.1068
randH target1: LHS 0.00012174964943679604 RHS 2Im K1 0.00012174964943680611 rel err 8.27068309727374e-14
randH target2: LHS (-5.554435986671317e-07+3.912564297375821e-22j) RHS (-5.554435986671382e-07+3.705769144237564e-21j) rel err 1.3069672708101129e-14
diagH,z=(I,2I) FD vs analytic D2 (5, 70, True) -0.007551870970473879 -0.007551866132438079 rel 6.406406861321697e-07
diagH,z=(I,2I) i=0 K1(+,+)= (0.04484601868904884-0.06505217583486961j) 2Im K1= -0.13010435166973922 |.|<=L1: 0.13010435166973922 <= 0.33995833560159605 conj check 0.0
diagH,z=(I,2I) target3: LHS -0.054972792482355676 RHS (-0.05497279248233762+0j) rel err 3.284352335523364e-13
diagH,z=(I,2I) target5: |LHS|=5.497279e-02 <= L1+L2 = 1.576829e-01 ; slack ratio 0.3486
diagH,z=(I,2I) target1: LHS -0.13010435166980447 RHS 2Im K1 -0.13010435166973922 rel err 5.015463159752868e-13
diagH,z=(I,2I) target2: LHS (1.0431760379660128e-05+0j) RHS (1.0431760379660138e-05-0j) rel err 9.743700964288029e-16
H=1,z=(I,2I) FD vs analytic D2 (5, 70, True) 0.0017037037037037038 0.0017037025124011507 rel 6.992428029258523e-07
H=1,z=(I,2I) i=0 K1(+,+)= (1.2361510991775469e-16-1.2361510991775469e-16j) 2Im K1= -2.4723021983550937e-16 |.|<=L1: 2.4723021983550937e-16 <= 6.992726598397183e-16 conj check 0.0
H=1,z=(I,2I) target3: LHS 3.3607681755927765e-05 RHS (3.360768175574362e-05+0j) rel err 5.479252156409306e-12
H=1,z=(I,2I) target5: |LHS|=3.360768e-05 <= L1+L2 = 1.680384e-04 ; slack ratio 0.2000
H=1,z=(I,2I) target1: LHS -2.4527363647053324e-16 RHS 2Im K1 -2.4723021983550937e-16 rel err 0.007977145008861123
H=1,z=(I,2I) target2: LHS (1.680384087791495e-05+0j) RHS (1.680384087791496e-05-0j) rel err 6.048852426596424e-16
randH,Im z1<0 target3: LHS -9.755295626347706e-05 RHS (-9.755295626346365e-05-3.8116482626443515e-21j) rel err 1.3739665523949812e-13
randH,Im z1<0 target1: LHS -0.00012174964943680703 RHS 2Im K1 -0.00012174964943680315 rel err 3.183600761534423e-14
randH,Im z1<0 target2: LHS (5.554435986671308e-07+2.884792386278684e-23j) RHS (5.554435986671382e-07-3.8116482626443515e-21j) rel err 1.5028480544123154e-14
```
(`target5` = bound of targets 4d/5.)

Every hypothesis of targets 1-5 and of the instances `inst_single`, `inst_single_diag`, `inst_wirtFirst_product`, `inst_contraction`, `inst_kernel_bound` (`H=1`), `inst_kernel_bound_Lt` (`diagH`) holds at this data; identities hold to relative error <= 5.5e-12 where the value is nonzero, the bound holds with ratio <= 0.35.

Verdicts: target 1 PASS; target 2 PASS; target 3 PASS; targets 4a, 4b, 4c, 4d PASS; target 5 PASS (4d with `L1t`, `L2t`, no extra hypothesis); target 6 (instances) PASS. Overall: **PASS**. (Names, Mathlib and builds are not checked at this stage.)

## (b) Script output — Tue Oct  6 04:54:15 UTC 2026

```
$ git log -1 --format=%h t/T2253; git diff --stat main...t/T2253
acb8eef
 RBM3D/Universality/OUContraction.lean | 1237 +++++++++++++++++++++++++++++++++
 1 file changed, 1237 insertions(+)
$ lake build RBM3D.Universality.OUContraction 2>&1 | tail -1
Build completed successfully (3353 jobs).
$ lake build   (worktree; root RBM3D.lean untouched, so this is main's library) | tail -1
Build completed successfully (4056 jobs).
$ grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Universality/OUContraction.lean; wc -l <file>
0
    1237 RBM3D/Universality/OUContraction.lean
$ lake env lean RBM3D/Universality/OUContraction.lean | grep axioms | sed ... | sort | uniq -c   (19 #print axioms lines at file end)
  19 [propext, Classical.choice, Quot.sound]
```

Target statements, extracted by script (python, file lines; `:= by` / `:=` terminates):
```
62: def paperK1Contraction (lam : ℝ) (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) (σ τ : Bool) : ℂ :=

69: def paperK2Contraction (lam : ℝ) (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z₁ z₂ : ℂ) (σ τ : Bool) : ℂ :=

78: theorem centeredVariance_single_contraction_eq (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ)
79:     (H : Matrix (Idx d L W) (Idx d L W) ℂ) (hH : H.IsHermitian)
80:     (z : ℂ) (hz : z.im ≠ 0) :
81:     (∑ a : Idx d L W, ∑ b : Idx d L W,
82:       (centeredVarianceEntry d L W lam a b : ℂ) *
83:         wirtSecond d L W (fun K => ((stieltjesN K z).im : ℂ)) H a b) =
84:       ((2 * (paperK1Contraction d L W lam H z true true).im : ℝ) : ℂ) := by

215: theorem centeredVariance_wirtingerFirst_product_eq (d L W : ℕ) [NeZero L] [NeZero W]
216:     (lam : ℝ)
217:     (H : Matrix (Idx d L W) (Idx d L W) ℂ) (hH : H.IsHermitian)
218:     (z₁ z₂ : ℂ) (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0) :
219:     (∑ a : Idx d L W, ∑ b : Idx d L W,
220:       (centeredVarianceEntry d L W lam a b : ℂ) *
221:         stieltjesImWirtingerFirst d L W H z₁ a b * stieltjesImWirtingerFirst d L W H z₂ b a) =
222:       -(1 / 4 : ℂ) *
223:         (paperK2Contraction d L W lam H z₁ z₂ true true -
224:           paperK2Contraction d L W lam H z₁ z₂ true false -
225:           paperK2Contraction d L W lam H z₁ z₂ false true +
226:           paperK2Contraction d L W lam H z₁ z₂ false false) := by

823: theorem centeredVariance_wirtProduct_contraction_eq (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ)
824:     {ι : Type*} [DecidableEq ι] (s : Finset ι)
825:     (H : Matrix (Idx d L W) (Idx d L W) ℂ) (hH : H.IsHermitian)
826:     (z : ι → ℂ) (hz : ∀ i ∈ s, (z i).im ≠ 0) :
827:     (∑ a : Idx d L W, ∑ b : Idx d L W,
828:       (centeredVarianceEntry d L W lam a b : ℂ) *
829:         wirtSecond d L W
830:           (fun K => ((∏ i ∈ s, (stieltjesN K (z i)).im : ℝ) : ℂ)) H a b) =
831:       (∑ i ∈ s,
832:         ((∏ j ∈ s.erase i, (stieltjesN H (z j)).im : ℝ) : ℂ) *
833:           ((2 * (paperK1Contraction d L W lam H (z i) true true).im : ℝ) : ℂ)) +
834:       ∑ i ∈ s, ∑ j ∈ s.erase i,
835:         ((∏ k ∈ (s.erase i).erase j, (stieltjesN H (z k)).im : ℝ) : ℂ) *
836:           (-(1 / 4 : ℂ) *
837:             (paperK2Contraction d L W lam H (z i) (z j) true true -
838:               paperK2Contraction d L W lam H (z i) (z j) true false -
839:               paperK2Contraction d L W lam H (z i) (z j) false true +
840:               paperK2Contraction d L W lam H (z i) (z j) false false)) := by

927: theorem paperK1Contraction_conj (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ)
928:     (H : Matrix (Idx d L W) (Idx d L W) ℂ) (hH : H.IsHermitian) (z : ℂ) :
929:     conj (paperK1Contraction d L W lam H z true true) =
930:       paperK1Contraction d L W lam H z false false := by

952: theorem paperK1Contraction_im_abs_le (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ)
953:     (H : Matrix (Idx d L W) (Idx d L W) ℂ) (hH : H.IsHermitian) (z : ℂ) :
954:     ‖((2 * (paperK1Contraction d L W lam H z true true).im : ℝ) : ℂ)‖ ≤
955:       paperL1Kernel d L W lam H z := by

976: theorem paperK2Contraction_abs_le (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ)
977:     (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z₁ z₂ : ℂ) :
978:     ‖-(1 / 4 : ℂ) *
979:         (paperK2Contraction d L W lam H z₁ z₂ true true -
980:           paperK2Contraction d L W lam H z₁ z₂ true false -
981:           paperK2Contraction d L W lam H z₁ z₂ false true +
982:           paperK2Contraction d L W lam H z₁ z₂ false false)‖ ≤
983:       paperL2Kernel d L W lam H z₁ z₂ := by

1013: theorem centeredVariance_wirtProduct_kernel_bound (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ)
1014:     {ι : Type*} [DecidableEq ι] (s : Finset ι)
1015:     (H : Matrix (Idx d L W) (Idx d L W) ℂ) (hH : H.IsHermitian)
1016:     (z : ι → ℂ) (hz : ∀ i ∈ s, 0 < (z i).im) :
1017:     ‖∑ a : Idx d L W, ∑ b : Idx d L W,
1018:         (centeredVarianceEntry d L W lam a b : ℂ) *
1019:           wirtSecond d L W
1020:             (fun K => ((∏ i ∈ s, (stieltjesN K (z i)).im : ℝ) : ℂ)) H a b‖ ≤
1021:       (∑ i ∈ s,
1022:         (∏ j ∈ s.erase i, (stieltjesN H (z j)).im) * paperL1Kernel d L W lam H (z i)) +
1023:       ∑ i ∈ s, ∑ j ∈ s.erase i,
1024:         (∏ k ∈ (s.erase i).erase j, (stieltjesN H (z k)).im) *
1025:           paperL2Kernel d L W lam H (z i) (z j) := by

1077: theorem centeredVariance_wirtProduct_kernel_bound_Lt (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ)
1078:     {ι : Type*} [DecidableEq ι] (s : Finset ι)
1079:     (H : Matrix (Idx d L W) (Idx d L W) ℂ) (hH : H.IsHermitian)
1080:     (z : ι → ℂ) (hz : ∀ i ∈ s, 0 < (z i).im) :
1081:     ‖∑ a : Idx d L W, ∑ b : Idx d L W,
1082:         (centeredVarianceEntry d L W lam a b : ℂ) *
1083:           wirtSecond d L W
1084:             (fun K => ((∏ i ∈ s, (stieltjesN K (z i)).im : ℝ) : ℂ)) H a b‖ ≤
1085:       (∑ i ∈ s,
1086:         (∏ j ∈ s.erase i, (stieltjesN H (z j)).im) * L1t d L W lam H (z i)) +
1087:       ∑ i ∈ s, ∑ j ∈ s.erase i,
1088:         (∏ k ∈ (s.erase i).erase j, (stieltjesN H (z k)).im) *
1089:           L2t d L W lam H (z i) (z j) := by

```

Instances: file lines 1100-1235, namespace `RBM.Univ.OUContractionInst` (`diagH`, `diagH_herm`, `diagH_nonscalar`, `inst_single`, `inst_single_diag`, `inst_wirtFirst_product`, `inst_contraction`, `inst_kernel_bound`, `inst_kernel_bound_Lt`; each `inst_*` states the `_at` body at `d=3, L=3, W=2, lam=1/2` explicitly and is proved by the target; hypotheses discharged: `Matrix.isHermitian_one`, `diagH_herm`, `by simp`, `fin_cases i <;> simp`; nothing left open). Nonscalar value (from (a), script): `2 Im K1(diagH, z=I; +,+) = -0.1301`.

Scratch check (`scratchpad/T2253/check_scratch.lean` = the check file with `import RBM3D.Universality.OUContraction` in place of `import RBM3D`, the `UNEMCTE2k` `#check` removed (`PinsK` not imported by this module), plus the defeq examples below):
```
$ lake env lean check_scratch.lean > scratch.out 2>&1; echo EXIT $?; grep -c error scratch.out
EXIT 0
0
(each line: `example : RBM.Univ.T2253Check.X := RBM.Univ.Y`; first three `example : RBM.Univ.Y = RBM.Univ.T2253Check.X := rfl`)
Y = X := rfl:  paperK1Contraction, paperK2Contraction, OUContractionInst.diagH = T2253_diagH
T2253_centeredVariance_single_contraction_eq := centeredVariance_single_contraction_eq  T2253_centeredVariance_wirtingerFirst_product_eq := centeredVariance_wirtingerFirst_product_eq
T2253_centeredVariance_wirtProduct_contraction_eq := centeredVariance_wirtProduct_contraction_eq  T2253_paperK1Contraction_conj := paperK1Contraction_conj
T2253_paperK1Contraction_im_abs_le := paperK1Contraction_im_abs_le  T2253_paperK2Contraction_abs_le := paperK2Contraction_abs_le
T2253_centeredVariance_wirtProduct_kernel_bound := centeredVariance_wirtProduct_kernel_bound  T2253_centeredVariance_wirtProduct_kernel_bound_Lt := centeredVariance_wirtProduct_kernel_bound_Lt
T2253_diagH_herm := diagH_herm  T2253_diagH_nonscalar := diagH_nonscalar
T2253_inst_single := inst_single  T2253_inst_single_diag := inst_single_diag
T2253_inst_wirtFirst_product := inst_wirtFirst_product  T2253_inst_contraction := inst_contraction
T2253_inst_kernel_bound := inst_kernel_bound  T2253_inst_kernel_bound_Lt := inst_kernel_bound_Lt

```
The last `example` of the check (consumer shape: target 5 at `Sizes d`, `s = univ : Finset (Fin nf)`, `lam = sz.lam n`) elaborates in the same run (EXIT 0).

Registry pre-check (`import RBM3D` + `import RBM3D.Universality.OUContraction` + `#assert_rbm_axioms`, temporary uncommitted scratch; same file without the second import = main):
```
$ lake env lean precheck.lean > precheck.out; echo EXIT $?   ;  lake env lean precheck_main.lean > precheck_main.out; diff precheck_main.out precheck.out
EXIT 0 (both)
1c1
< axiom audit: 7497 theorems, 2530 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
---
> axiom audit: 7518 theorems, 2533 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 154 (borrowed 1, owed 98, structural 38, refuted 6, superseded 11).
registry: 2 borrowed + 157 owed + 98 structural + 7 refuted + 12 superseded; 122 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
$ git diff --stat main...t/T2253 -- RBM3D/Test/Axioms.lean   (empty)
```

Name-clash grep (`grep -rnw <name> RBM3D RBM3D.lean`, outside the new file, non-Probe; count of hits):
```
paperK1Contraction:        0
paperK2Contraction:        0
centeredVariance_single_contraction_eq:        0
centeredVariance_wirtingerFirst_product_eq:        0
centeredVariance_wirtProduct_contraction_eq:        0
centeredVariance_wirtProduct_kernel_bound:        0
centeredVariance_wirtProduct_kernel_bound_Lt:        0
paperK1Contraction_conj:        0
paperK1Contraction_im_abs_le:        0
paperK2Contraction_abs_le:        0
OUContractionInst:        0
diagH:        0
OUContraction_ prefix outside:        0
1
$ ls RBM3D/Universality | grep -c "^OUContraction.lean"  -> 1 (the new file only)
```
Port source: RBM2D `Universality/OUContraction.lean` at `c9a24cf` (1109 lines; read with `git show c9a24cf:...`).
```
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks log -1 --format=%h
9e0f275
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Universality/OUContraction.lean
 RBM2D/Universality/OUContraction.lean | 90 +++++------------------------------
 1 file changed, 12 insertions(+), 78 deletions(-)
```

### Narrative (port, 2026-10-06; every figure above is script output)
- The file is a mechanical port of RBM2D `OUContraction.lean` at `c9a24cf`: `Idx L W` to `Idx d L W`, `(L W : ℕ)` to `(d L W : ℕ)`, new explicit `lam : ℝ` after the instances in every public statement and in the two vocabulary defs, `wirtSecond`/`stieltjesImWirtingerFirst`/`RBM.Green.Bmat`/`Bmat_swap_*` and the UN-16 formulas called with `d L W`. A script (`scratchpad/T2253/conv.py`, `conv2.py`) did the renaming; the rest was edited by hand.
- Statements are as in the check file (`T2253_*_at` bodies unfolded); the check's defeq examples compile (EXIT 0, 0 errors), so no statement difference to the check.
- Changes beyond renaming: (1) `RBM.Gsig_conjTranspose` replaced by private `OUContraction_green_conj` (body of `OUHessian_green_conj`, `OUHessian.lean:83-87`), used in `paperK1Contraction_conj` through `simp only [signedGreen, ↓reduceIte]; exact`; (2) `OUContraction_K1_conj_eq_false_false`, `_K1_im_abs_le`, `_K2_abs_le` are now the public `paperK1Contraction_conj`, `paperK1Contraction_im_abs_le`, `paperK2Contraction_abs_le` (explicit `d L W lam H`); (3) new `centeredVariance_wirtProduct_kernel_bound_Lt` by `simpa only [paperL1Kernel_eq_L1t, paperL2Kernel_eq_L2t] using` target 4d; (4) private `OUContraction_cross_contraction_eq` takes `lam` explicitly (it is not determined by `hH`, `z`), and its call site passes it; (5) `open RBM.Endpoints` dropped; (6) `set_option linter.style.longLine false` added (as `OUHessian.lean`).
- Lean drift (preflight (iii)): `simp [q, ...]` unfolded `Fintype.card (Idx d L W)` to `(W*L)^d` in the two sites of `OUContraction_lineFirst_wirtinger` (RBM2D `:466-470`, `:482-486`). Fix at both: `obtain ⟨q, hqd⟩ : ∃ q : ℂ, q = (Fintype.card (Idx d L W) : ℂ)⁻¹ := ⟨_, rfl⟩; rw [← hqd]` instead of `let q`, `hq` by `rw [hqd]; simp only [Complex.inv_im, Complex.natCast_im, zero_div, neg_zero]`, and `hqd` instead of `q` in the `simp` sets. Target 2's `hc` step needed no change; `if_neg` is not used (RBM2D already uses `ite_eq_right`).
- `diagH_nonscalar`: `decide` on `ZMod.val (x0 0) = 0`, `ZMod.val (x1 0) = 1`, then `simp only [diagH, Matrix.diagonal_apply_eq, h0, h1]; norm_num` (`simp` alone rewrites `ZMod.val 1` to a `ZMod.cast` and stalls).
- Not targets, not touched: every pin (`UNEMCTE2`, `UNEMCTE2Row`, `UNEMCTE2k`, `UNUnivMainRow` stay owed: UN-18, UN-24), anything with `ouP`/`ouMat` or an integral (UN-15), merged files (the conj bridge is a private copy), a public `stieltjesN_im_nonneg` (kept private as `OUContraction_stieltjesN_im_nonneg`), the C form, refuted pins. `Test/Axioms.lean` is unchanged (diff empty).
- The theorems assume only `H.IsHermitian` and `z.im ≠ 0` / `0 < z.im`; no unregistered premise (pre-check: premise counts identical to main; only the theorem/definition counts moved, 7497 to 7518 theorems and 2530 to 2533 definitions).
- Instances use `d = 3`, `L = 3`, `W = 2` (`N = 216`), `lam = 1/2`; the `H = 1` instance is `inst_kernel_bound` (the row sums of `S°` vanish there, so `K1 = 0`, per (a)); `inst_single_diag`, `inst_wirtFirst_product`, `inst_contraction`, `inst_kernel_bound_Lt` use the non-scalar `diagH`.
- Root import to add by the hub after `import RBM3D.Universality.OUHessian` (`RBM3D.lean`); the full `lake build` of this worktree does not include the new module until then (the module build above does).

## (c) Verified Mathlib names (all compile in the file; each used at the site shown)
`Complex.abs_im_le_norm`, `norm_sum_le`, `Finset.prod_nonneg`, `Matrix.isHermitian_diagonal_of_self_adjoint`, `Matrix.isHermitian_one`, `Matrix.trace_single_mul`, `Matrix.conjTranspose_mul`, `Matrix.conjTranspose_nonsing_inv`, `Matrix.diagonal_apply_eq`, `Complex.inv_im`, `Complex.natCast_im`, `Finset.sum_comm`, `Fintype.sum_prod_type`, `Fintype.sum_bool`, `Complex.norm_real`, `norm_mul`, `norm_add_le`, `norm_sub_le`, `ite_eq_left`, `ite_eq_right`. Verified absent: none needed (no invented names).

## (d) Open issues and paper-delta candidates
- No open issue; no target failed. No statement difference to the paper statement or to the check (no new paper-delta expected).
- T2253a (design, no paper statement, as the ticket): (1) UN-15 and UN-17 are each imported only by UN-18 in RBM2D; (2) only UN-18 calls `paperL1Kernel_eq_L1t`/`paperL2Kernel_eq_L2t` (UN-17 does not); (3) three RBM2D private lemmas are public here (`paperK1Contraction_conj`, `paperK1Contraction_im_abs_le`, `paperK2Contraction_abs_le`) and one corollary is new (`centeredVariance_wirtProduct_kernel_bound_Lt`); (4) for the UN-15 drafter: RBM3D carrier is model-generic (`Pins.lean:145-152`).
- T2253b: none.
- Not done by this stage: the hub's full `lake build` with the root import (CLAUDE.md §3 (A)).
