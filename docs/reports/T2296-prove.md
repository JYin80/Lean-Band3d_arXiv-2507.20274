Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 12:55:38 UTC 2026

### (i) Exponent table

No pin is proved. Every constant below is a merged definition read from the files; the 11 targets depend on these only.

| Quantity | Value / definition (source) | Constraint | Slack at the instance of (ii) (d=3, k=1, Lambda=2, kappa=0.3) |
|---|---|---|---|
| `c = BAct_rate d Λ κ` (CombesThomas.lean:45) | `min (log(1+κ/(4dΛ))) (κ/2)` | `c > 0` needs `0<d, 0<Λ, 0<κ` (`BAct_rate_pos`:52); paper (Mbound_AO2) `7_8:1902` | `c = 0.012423`, `c <= κ/2 = 0.15`; depends on `(d,Λ,κ)` only, not on `L, W, n, g0, E, m` |
| `expC k c` (RadialSum.lean:271) | `2^(k+2)·2·(2^(k+3)(1+(k+3)!/c^(k+3)))` | `c > 0`, `d = k+2`; uniform in `L` (`sum_radial_exp_decay_le`:275) | `expC 1 c = 2.580e11` |
| row constant `K = c⁻¹ expC k c` (targets 6, 7) | product of the two rows above | none beyond `c>0`; independent of `L, W` | `K = 2.077e13` vs actual `max_a Σ_b |M^(B)_ab| = 5.93` (very non-sharp, only uniformity is claimed) |
| `|M^(B)_ab| <= c⁻¹ e^{-c|a-b|}` (target 5) | `BAMB_decay_large` (CombesThomas.lean:509), every `0<g<=Λ`, no branch premise | `3<=L`, `0<d`, `0<g<=Λ`, `0<κ`, `BAReal` | actual max ratio `0.0071` (<= 1) |
| `C = 16d²/κ³` (BAct_C :42) | small-g branch `g<(2C)⁻¹` | not used by any target (large-branch bound holds for every `g<=Λ`) | n/a |
| `t0 = BAt0 z m = Im m/(Im m + Im z)` (MFixedPoint.lean:279) | flow time | `0<t0<1` needs `Im z>0, Im m>0` (`BAzztE_data`:297) | `t0_n ∈ [0.92016, 0.9999999999998]` over the sampled `n` |
| `g0 = √t0 · lam_n` (`BAflowLam0`, FlowPins.lean:543) | flow coupling | target 2: `0<g0<=𝔡⁻¹`, eventually; `√t0<=1`, `lam_n>0` eventually | `g0_n ∈ [0.9592, 1.0000]`, `𝔡⁻¹=2`: slack `>= 1` |
| `(eq:WO)` threshold `W^{-d/2+𝔡}<=lam_n<=𝔡⁻¹` (Sizes.lean:164) | eventual in `n`; gives `lam_n>0` (`W>=1`) | `𝔡=1/2`, `lam_n=1`: `W_n^{-1}<=1<=2` | lower slack `1-1/W_n >= 0.5`; upper slack `1` |
| `Bandwidth 𝔠` (`W>=N^𝔠`, Sizes.lean:168) | eventual | `𝔠=1/6`, `L_n=4`: `W>=(4W)^{1/2}` iff `W>=4` | holds for `n>=2` (`W_n=n+2`); equality at `W=4` |
| `ε` in `N^{-1+ε}<=Im z_n<=1` (`BAdom`, MFixedPoint.lean:435) | every `n` | `ε=1/2`, `z_n=0.5+i N_n^{-1/2}` | equality in the lower bound by choice; upper slack `0.956` at `n=0` |
| `κ <= Im m(z_n,lam_n)` (`BAdom`) | every `n` | `κ=0.3` | `min_n Im m(z_n)=0.50931` (n=0), limit `η→0`: `0.52722`; slack `>=0.209`. Then `Im m0 = 0.53095>=κ`, slack `0.231` (target 1, `√t0<=1`) |
| `t<1` (target 8) | any real `t<1` (also `t<0`: `√t=0`) | `Im z_t=(1-t)Im m>0`; `Im(E+m)=Im m>0` | `t=0.5`: `Im z_t=0.2655`. Identity `A-B=H_flow+t m` holds for all real `t` (algebra, no constraint) |
| Ward `Σ_b|M^(B)_ab|²=1` (`BAMB_ward_row`, Ward.lean:108, `Im z=0`) | gives `|M^(B)_ab|<=1` (target 4) | `BASelf` (`Im m>0`) | `max|M|=0.5717`, slack `0.428` |
| `3<=L`, `0<d`, `d=k+2` | targets 5, 6, 7 only; 1-4, 8-11 hold for any `d`, `L` | `L=4`, `d=3` | 1 |

Checks against the paper (math only): (def_G0) `1_2:631`: `M=(λΨ−z−m)⁻¹=M^(B)⊗I_{W^d}`, targets 3 restates it, nothing stronger. (Mbound_AO2) `7_8:1902` `|M^(B)_ab|<=c⁻¹exp(−c|a−b|)` is stated for `λ>=(2C)⁻¹`; target 5 is the Lean-proved version for every `0<g<=Λ` with `c` depending on `(d,Λ,κ)` (stronger-in-range, same shape; D4 = T2290). Targets 6, 7 (ℓ¹ rows) are consequences of (Mbound_AO2) and the lattice sum, not paper statements. Flow: `H_t=g0Ψ+√tV`, `z_t=E+(1−t)m` (`1_2:685`, `:716`), `G_t−M=−M(√tV+tm)G_t` follows from `B−A` below. Targets 10, 11 are algebra of Schur (4.7)/(4.8) for `H=D+X` (`EntryCore.lean:242,255`); not a paper statement beyond the BA split.

Math of the non-obvious targets (each checked against the files):
- Target 1 (every n): `Im z_n >= N_n^{-1+ε} > 0` since `N_n=sz.size n>=1`; `BAm_self` gives `BASelf` at `z_n`; `BAdom_real` (MFixedPoint.lean:479) gives `BAReal` at `(√t0 lam_n, κ, E(z_n), m/√t0)`; these are `BAflowLam0, BAflowEs` by definition; `BAmF = m/√t0` by `BAm_real_eq_of_self` (:824). No use of `𝔠, 𝔡, ε` beyond `BAdom`. Target 2: `lam_n>0` eventually (from `WO`, `W>=1`), `t0>0` so `√t0>0`, `√t0<=1` (`t0<1`), so `0<g0<=lam_n<=𝔡⁻¹`.
- Target 3: `BAMres_fine_apply` (BA/FlowPins.lean:100) needs `(z+m).im≠0`; here `z=(E:ℂ)`, `Im m>0`. Target 4: Ward at `Im z=0` gives `Σ|M^B|²=1`, one term `<=1`; off-fibre entries are `0`. Target 5: off-fibre `0<=` positive RHS; same fibre `BAMB_decay_large`.
- Targets 6-7: `Σ_b c⁻¹e^{-c|a−b|}=c⁻¹Σ_x e^{-c|x|}<=c⁻¹expC`; target 7: for fixed `x`, `y↦(split y).1` is a bijection of the fibre `{(split y).2=(split x).2}` onto `Zd d L` (`split` injective, `splitEquiv` bijective, Vtx=`Zd×Fin(W^d)`), other `y` give `0`.
- Target 8: `A=H_t−z_t`, `B=g0Ψ−(E+m)` units (Hermitian + nonreal shift; `isUnit_sub_smul_of_isHermitian`); `A−B=seqHflow+t m·1=BAflowPert` for every real `t` (`z_t−(E+m)=−t m`); then `A⁻¹−B⁻¹=−B⁻¹(A−B)A⁻¹=−A⁻¹(A−B)B⁻¹`.
- Target 9: `Ψ=Ψ^B⊗I`, `Ψ^B_aa=0` because `Adj a a` means `zdistD 0=1` and `zdistD 0=0`.
- Targets 10-11: with `D_ik=0` for `b i=b k`, `X_ik=0` for `b i≠b k`: `H_ii=X_ii` (`D_ii=0`), `H_ik=X_ik` for `b k=b i`, `=D_ik` otherwise; same for `H_li`; split each sum by `b k=b i`. All four products of (4.7) are present, `X_li=0`/`D_li=0` by the hypotheses at `(l,i)`. Instance (I3) of the ticket checked by hand: `ι=Fin 2, b=id, X=0, D=[[0,1],[1,0]], z=i`: `det(H−z)=(−i)²−1=−2` (unit), `G=[[i/2,1/2],[1/2,i/2]]`, `G_00=i/2≠0`; (4.7): minor `G^(0)=1/(−i)=i`, `q=1·i·1=i`, `(0−i−i)⁻¹=i/2` OK.

### (ii) One concrete nondegenerate instance

`d=3` (k=1), `L_n=4`, `W_n=n+2`, `lam_n=1`, `𝔠=1/6`, `𝔡=1/2`, `ε=1/2`, `κ=0.3`, `Λ=𝔡⁻¹=2`, `z_n=0.5+i N_n^{-1/2}`, `N_n=(4W_n)^3`. Pointwise targets 3-11 at `n=0` (`W=2`, `N=512`, `w=8`, `E`, `g0`, `m0` from the flow of `z_0`, `t=0.5`, `V`=GUE blocks of size 8 scaled `8^{-1/2}`, zero off-block, seed 0). `Bandwidth` and `WO` are eventual predicates: they hold for `n>=2` (rows 'False' for `n=0,1` below are expected). External-limit computation (the `BAdom` hypothesis for all `n`): `Im m(0.5+iη)` for the `η=N_n^{-1/2}` of 65 sampled `n` is within `[0.5093, 0.5273]`, and the limit `η→0` is `0.52722` (script below), so `κ=0.3` holds with slack `>=0.209` for every `n`.

Command: `python3 inst.py` (numpy 2.0.2; scratch in the scratchpad) and `python3 grid.py`. Output verbatim:

```
== (ii) flow instance: d=3, L_n=4, W_n=n+2, lam_n=1, z_n=0.5+i N_n^{-1/2}, eps=1/2, c_=1/6, d_=1/2
n=0 W=2 N=512 eta=4.419e-02 Im m(z_n)=0.509310 resid=1.2e-16 Bandwidth W>=N^c: False WO: 5.000e-01<=lam<=1/d_=2.0
n=1 W=3 N=1728 eta=2.406e-02 Im m(z_n)=0.517281 resid=0.0e+00 Bandwidth W>=N^c: False WO: 3.333e-01<=lam<=1/d_=2.0
n=2 W=4 N=4096 eta=1.562e-02 Im m(z_n)=0.520713 resid=2.8e-17 Bandwidth W>=N^c: True WO: 2.500e-01<=lam<=1/d_=2.0
n=5 W=7 N=21952 eta=6.749e-03 Im m(z_n)=0.524388 resid=1.1e-16 Bandwidth W>=N^c: True WO: 1.429e-01<=lam<=1/d_=2.0
n=50 W=52 N=8998912 eta=3.334e-04 Im m(z_n)=0.527083 resid=0.0e+00 Bandwidth W>=N^c: True WO: 1.923e-02<=lam<=1/d_=2.0
n=1000 W=1002 N=64384768512 eta=3.941e-06 Im m(z_n)=0.527222 resid=2.8e-17 Bandwidth W>=N^c: True WO: 9.980e-04<=lam<=1/d_=2.0
n=100000 W=100002 N=64003840076800512 eta=3.953e-09 Im m(z_n)=0.527224 resid=1.2e-16 Bandwidth W>=N^c: True WO: 1.000e-05<=lam<=1/d_=2.0
limit eta->0 (eta=1e-14): m = (-0.21649969220777976+0.5272235955628883j) resid 7.972423723352112e-15
kappa = 0.3  min sampled Im m(z_n) = 0.5093096579040247  slack 0.20930965790402473
n=0: t0=0.920156 (0<t0<1) E_flow=0.496560 g0=0.959247 (0<g0<=lam=1<=1/d_=2) m0=(-0.21211546915730006+0.5309471227778226j)
Target1: BASelf resid at (g0,E_flow,m0): 2.3714374201337736e-16  Im m0 = 0.5309471227778226 >= kappa: True  slack 0.23094712277782264
   BAmF (continuation to real axis) vs m0: 5.234851668643258e-15
Constants: Lambda=2.0 kappa=0.3 c=BAct_rate=0.012423 (<=kappa/2=0.15) expC(1,c)=2.579957e+11 K=c^-1 expC=2.076838e+13
Target 3/4/5/6 on M^(B) (L=4):
  Ward max_a|sum_b|M_ab|^2-1| = 1.7763568394002505e-15
  max|M_ab| = 0.5717497874436597 <= 1
  max |M_ab|/(c^-1 e^{-c|a-b|}) = 0.0071025731686896396 <= 1
  max_a sum_b |M_ab| = 5.929637551798331 <= K = 20768383017088.086
Fine lattice n=0: N=512, w=8
Target 3: max|M_fine - M^B (x) I| = 6.703129537951225e-16
Target 7: max_x sum_y |M_xy| = 5.929637551798331 <= K
Target 9: max|PsiI in-block| = 0.0
Target 8 (t=0.5<1, Im z_t=0.2655>0): max|G-M+M Pert G| = 2.821392146820665e-15  max|G-M+G Pert M| = 2.5584860161789698e-15
Target 10: |G_ii - (X_ii - z - (qXX+qXD+qDX+qDD))^-1| = 1.1325499295668598e-15  |q - sum| = 4.577566798522237e-16  |G_ii|= 0.5745610616467413
Target 11: max_j |G_ij - rhs| = 2.9893669801409083e-16
n in 0..59 and 1e3..1e8: min Im m(z_n) = 0.5093096579040247  max Im m = 0.5272235955628397
g0_n=sqrt(t0_n)*lam: min 0.9592474204199574 max 0.9999999999998814  (need 0<g0<=1/d_=2); t0 range 0.9201556135823424 0.9999999999997629
```

Verdicts (math only; no Lean written):
- Target 1 `BAflow_real`: PASS. Target 2 `BAflow_lam0_window`: PASS (eventual in `n`, as `(eq:WO)`).
- Target 3 `BAMfine_eq`: PASS. Target 4 `BAMfine_norm_le_one`: PASS. Target 5 `BAMfine_decay`: PASS.
- Target 6 `BAMB_row_l1`: PASS. Target 7 `BAMfine_row_l1`: PASS.
- Target 8 `BAGt_sub_BAMfine`: PASS (both orders, every real `t<1`).
- Target 9 `BAPsiI_inBlock`: PASS. Target 10 `green_diag_split`: PASS. Target 11 `green_off_split`: PASS.
- Nonempty-hypothesis check: every hypothesis set is satisfied at the instance above (BAFlow's eventual clauses from `n>=2`; the real-axis data at `n=0`); no `N=0`, empty index, collapsed window. Instance (I3) of the ticket: hand computation above gives `G_00=i/2≠0` (nonvacuous, `X=0` is a legitimate data point).

## (b) Script output
Generated Tue Oct  6 13:22:01 UTC 2026; worktree /Users/junyin/Lean_proof/RBM3D-wt/T2296, branch t/T2296; file RBM3D/BA/GreenSchur.lean (615 lines).
```
$ git log --oneline -4; git diff --stat main...t/T2296; git status --short | wc -l
1bc0c0c T2296: BA/GreenSchur, size data of the BAFlow instance private
e071066 T2296: BA/GreenSchur, nondegeneracy facts for the Psi instance
3eaf6b9 T2296: BA/GreenSchur, BAFlow instance for targets 1, 2
8b403a5 T2296: BA-G1 BA/GreenSchur (Schur structure of the block Anderson resolvent, deterministic hopping)
 RBM3D/BA/GreenSchur.lean | 615 +++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 615 insertions(+)
       0
$ lake build RBM3D.BA.GreenSchur 2>&1 | grep -E "^error|sorry|Build completed"
Build completed successfully (3742 jobs).
$ lake env lean RBM3D/BA/GreenSchur.lean; echo exit=$?     # full elaboration, no output = no error, no warning
exit=0
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/BA/GreenSchur.lean; echo "grep exit=$?"     # 1 = no match
grep exit=1
$ lake env lean axioms.lean   # `#print axioms` of the 11 targets, BAflowPert, 12 instance theorems (24 lines)
exit=0
$ sed "s/.*depends on axioms: //" axioms.out | sort | uniq -c
  24 [propext, Classical.choice, Quot.sound]
$ sed "s/ depends.*//; s/.RBM.BA.//; s/.//" axioms.out | tr "\n" " "
BAflow_real BAflow_lam0_window BAMfine_eq BAMfine_norm_le_one BAMfine_decay BAMB_row_l1 BAMfine_row_l1 
BAGt_sub_BAMfine BAPsiI_inBlock green_diag_split green_off_split BAflowPert inst_row_l1 inst_Mfine_eq inst_Mfine_norm 
inst_Mfine_decay inst_Mfine_row_l1 inst_Gt_sub_Mfine inst_PsiI_inBlock inst_green_diag inst_green_off inst_BAFlow 
inst_flow_real inst_flow_window 
$ python3 mkcheck.py  # check-file imports + `import RBM3D.BA.GreenSchur`, check-file BAflowPert def deleted (pins use RBM.BA.BAflowPert), + 11 examples `example ... : Y_pin := @RBM.BA.Y`
$ grep -c "^example" checkeq.lean; lake env lean checkeq.lean > checkeq.out 2>&1; echo exit=$?; grep -c error checkeq.out
11
exit=0
0
$ grep -o "^example.*" checkeq.lean | sed "s/.*:= //" | tr "\n" " "
@RBM.BA.BAflow_real d @RBM.BA.BAflow_lam0_window d @RBM.BA.BAMfine_eq d @RBM.BA.BAMfine_norm_le_one d @RBM.BA.BAMfine_decay d @RBM.BA.BAMB_row_l1 @RBM.BA.BAMfine_row_l1 @RBM.BA.BAGt_sub_BAMfine d @RBM.BA.BAPsiI_inBlock @RBM.BA.green_diag_split @RBM.BA.green_off_split 
$ cat precheck.lean   # registry pre-check, temporary file outside the repo
import RBM3D
import RBM3D.BA.GreenSchur
#assert_rbm_axioms
$ lake env lean precheck.lean > precheck.out 2>&1; echo exit=$?; sed -n "1p;154p" precheck.out
exit=0
axiom audit: 8524 theorems, 2796 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 153 (borrowed 1, owed 94, structural 41, refuted 6, superseded 11).
$ same with `import RBM3D` alone (precheck0.lean): exit, sed -n "1p;154p"
exit=0
axiom audit: 8501 theorems, 2795 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 153 (borrowed 1, owed 94, structural 41, refuted 6, superseded 11).
$ lake build 2>&1 | tail -1     # full library in the T2296 worktree (RBM3D.lean does not yet import the new module; the hub adds it)
Build completed successfully (4102 jobs).
$ bash clash2.sh   # grep -rlw of each new public name over RBM3D/*.lean outside the new file; git grep -lw on t/T2295; docs/tickets T2295/T2297/T2298
files outside GreenSchur.lean containing the name (grep -rlw, RBM3D/, worktree = main 59a0ab5):
 BAflow_real=0 BAflow_lam0_window=0 BAMfine_eq=0 BAMfine_norm_le_one=0 BAMfine_decay=0 BAMB_row_l1=0 BAMfine_row_l1=0 
BAflowPert=0 BAGt_sub_BAMfine=0 BAPsiI_inBlock=0 green_diag_split=0 green_off_split=0 GreenSchurInst=0 inst_BAFlow=0 
inst_flow_real=0 inst_flow_window=0 inst_row_l1=0 inst_Mfine_eq=0 inst_Mfine_norm=0 inst_Mfine_decay=0 
inst_Mfine_row_l1=0 inst_Gt_sub_Mfine=0 inst_PsiI_inBlock=0 inst_green_diag=0 inst_green_off=0
GreenSchur_ substring: 0
git grep -lw on t/T2295 (tip d57aa36), same names:
 BAflow_real=0 BAflow_lam0_window=0 BAMfine_eq=0 BAMfine_norm_le_one=0 BAMfine_decay=0 BAMB_row_l1=0 BAMfine_row_l1=0 
BAflowPert=0 BAGt_sub_BAMfine=0 BAPsiI_inBlock=0 green_diag_split=0 green_off_split=0 GreenSchurInst=0 GreenSchur_=0 
inst_BAFlow=0 inst_flow_real=0
docs/tickets T2295 T2297 T2298 .md: 0 files
$ grep -n "^import" RBM3D/BA/GreenSchur.lean; ports from ../RBM1D, ../RBM2D: none (nothing copied from them, no command run there)
6:import RBM3D.BA.CombesThomas 7:import RBM3D.BA.ImmLower 8:import RBM3D.BA.FlowPins 9:import RBM3D.Green.EntryCore 10:import RBM3D.Defs.RadialSum 11:import RBM3D.Analysis.Resolvent 
$ lake env lean GS_noimm.lean 2>&1 | grep -m2 error   # the same file without `import RBM3D.BA.ImmLower`
GS_noimm.lean:361:5: error: unknown namespace `RBM.BA.CouplingWindowInst`
GS_noimm.lean:365:37: error(lean.unknownIdentifier): Unknown identifier `flowP_data`
$ grep -c "BAm_im_lower\|BAImmLower\|baImmLower" RBM3D/BA/GreenSchur.lean
0
```
### The 11 targets and `BAflowPert`, extracted from RBM3D/BA/GreenSchur.lean (python3 extract.py targets)
```lean
theorem BAflow_real {d : ℕ} (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ) (h : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) :
    BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n)
      (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) := by
theorem BAflow_lam0_window {d : ℕ} (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ) (h : BAFlow sz κ ε 𝔠 𝔡 z) :
    ∀ᶠ n in atTop, 0 < BAflowLam0 sz z n ∧ BAflowLam0 sz z n ≤ 𝔡⁻¹ := by
theorem BAMfine_eq {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (hm : 0 < (BAmF sz lam0 E n).im)
    (x y : Idx d (sz.L n) (sz.W n)) :
    BAMfine sz lam0 E n x y =
      if (split d (sz.L n) (sz.W n) x).2 = (split d (sz.L n) (sz.W n) y).2 then
        BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)
          (split d (sz.L n) (sz.W n) x).1 (split d (sz.L n) (sz.W n) y).1
      else 0 := by
theorem BAMfine_norm_le_one {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)
    (h : BASelf d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n))
    (x y : Idx d (sz.L n) (sz.W n)) : ‖BAMfine sz lam0 E n x y‖ ≤ 1 := by
theorem BAMfine_decay (d : ℕ) (hd : 0 < d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) (sz : Sizes d)
    (lam0 E : ℕ → ℝ) (n : ℕ) (hL : 3 ≤ sz.L n) (hg : 0 < lam0 n) (hgΛ : lam0 n ≤ Λ)
    (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) (x y : Idx d (sz.L n) (sz.W n)) :
    ‖BAMfine sz lam0 E n x y‖ ≤ (BAct_rate d Λ κ)⁻¹ *
      Real.exp (-BAct_rate d Λ κ *
        (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) x).1 - (split d (sz.L n) (sz.W n) y).1) : ℝ)) := by
theorem BAMB_row_l1 (k L : ℕ) [NeZero L] (hL : 3 ≤ L) (Λ g κ E : ℝ) (m : ℂ) (hΛ : 0 < Λ) (hg : 0 < g)
    (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hr : BAReal (k + 2) L g κ E m) (a : Zd (k + 2) L) :
    ∑ b : Zd (k + 2) L, ‖BAMB (k + 2) L g (E : ℂ) m a b‖ ≤
      (BAct_rate (k + 2) Λ κ)⁻¹ * expC k (BAct_rate (k + 2) Λ κ) := by
theorem BAMfine_row_l1 (k : ℕ) (sz : Sizes (k + 2)) (lam0 E : ℕ → ℝ) (n : ℕ) (Λ κ : ℝ) (hL : 3 ≤ sz.L n)
    (hΛ : 0 < Λ) (hg : 0 < lam0 n) (hgΛ : lam0 n ≤ Λ) (hκ : 0 < κ)
    (hr : BAReal (k + 2) (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) (x : Idx (k + 2) (sz.L n) (sz.W n)) :
    ∑ y : Idx (k + 2) (sz.L n) (sz.W n), ‖BAMfine sz lam0 E n x y‖ ≤
      (BAct_rate (k + 2) Λ κ)⁻¹ * expC k (BAct_rate (k + 2) Λ κ) := by
noncomputable def BAflowPert {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
theorem BAGt_sub_BAMfine {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (ht : t < 1)
    (hm : 0 < (BAmF sz lam0 E n).im) :
    BAGt sz lam0 E n t ω - BAMfine sz lam0 E n =
        -(BAMfine sz lam0 E n * BAflowPert sz lam0 E n t ω * BAGt sz lam0 E n t ω) ∧
      BAGt sz lam0 E n t ω - BAMfine sz lam0 E n =
        -(BAGt sz lam0 E n t ω * BAflowPert sz lam0 E n t ω * BAMfine sz lam0 E n) := by
theorem BAPsiI_inBlock (d L W : ℕ) [NeZero L] [NeZero W] (x y : Idx d L W)
    (h : (split d L W x).1 = (split d L W y).1) : PsiI d L W x y = 0 := by
theorem green_diag_split {ι β : Type} [Fintype ι] [DecidableEq ι] [DecidableEq β] (b : ι → β)
    (D X : Matrix ι ι ℂ) (z : ℂ) (hD : ∀ i k, b i = b k → D i k = 0) (hX : ∀ i k, b i ≠ b k → X i k = 0)
    (hU : IsUnit (D + X - z • (1 : Matrix ι ι ℂ)).det) (i : ι) (hGii : RBM.green (D + X) z i i ≠ 0) :
    RBM.green (D + X) z i i =
      (X i i - z -
        ((∑ k ∈ Finset.univ.filter (fun k : {a : ι // a ≠ i} => b k.1 = b i),
            ∑ l ∈ Finset.univ.filter (fun l : {a : ι // a ≠ i} => b l.1 = b i),
              X i k.1 * RBM.Green.minorGreen (RBM.green (D + X) z) i k l * X l.1 i) +
         (∑ k ∈ Finset.univ.filter (fun k : {a : ι // a ≠ i} => b k.1 = b i),
            ∑ l ∈ Finset.univ.filter (fun l : {a : ι // a ≠ i} => b l.1 ≠ b i),
              X i k.1 * RBM.Green.minorGreen (RBM.green (D + X) z) i k l * D l.1 i) +
         (∑ k ∈ Finset.univ.filter (fun k : {a : ι // a ≠ i} => b k.1 ≠ b i),
            ∑ l ∈ Finset.univ.filter (fun l : {a : ι // a ≠ i} => b l.1 = b i),
              D i k.1 * RBM.Green.minorGreen (RBM.green (D + X) z) i k l * X l.1 i) +
         (∑ k ∈ Finset.univ.filter (fun k : {a : ι // a ≠ i} => b k.1 ≠ b i),
            ∑ l ∈ Finset.univ.filter (fun l : {a : ι // a ≠ i} => b l.1 ≠ b i),
              D i k.1 * RBM.Green.minorGreen (RBM.green (D + X) z) i k l * D l.1 i)))⁻¹ := by
theorem green_off_split {ι β : Type} [Fintype ι] [DecidableEq ι] [DecidableEq β] (b : ι → β)
    (D X : Matrix ι ι ℂ) (z : ℂ) (hD : ∀ i k, b i = b k → D i k = 0) (hX : ∀ i k, b i ≠ b k → X i k = 0)
    (hU : IsUnit (D + X - z • (1 : Matrix ι ι ℂ)).det) (i : ι) (hGii : RBM.green (D + X) z i i ≠ 0)
    (j : {a : ι // a ≠ i}) :
    RBM.green (D + X) z i j.1 = -RBM.green (D + X) z i i *
      ((∑ k ∈ Finset.univ.filter (fun k : {a : ι // a ≠ i} => b k.1 = b i),
          X i k.1 * RBM.Green.minorGreen (RBM.green (D + X) z) i k j) +
       (∑ k ∈ Finset.univ.filter (fun k : {a : ι // a ≠ i} => b k.1 ≠ b i),
          D i k.1 * RBM.Green.minorGreen (RBM.green (D + X) z) i k j)) := by
```
### The compiled nonempty instances: bodies of the 12 theorems in `RBM.BA.GreenSchurInst` (python3 extract.py inst; statements at the cited lines)
```lean
theorem inst_BAFlow : BAFlow GreenSchur_szF (9 / 10) (1 / 2) (1 / 9) (1 / 2) GreenSchur_zF := by   (statement line 542; tactic proof)
-- inst_flow_real (statement lines 602-605)
  BAflow_real (9 / 10) (1 / 2) (1 / 9) (1 / 2) GreenSchur_szF GreenSchur_zF inst_BAFlow n
-- inst_flow_window (statement lines 608-610)
  BAflow_lam0_window (9 / 10) (1 / 2) (1 / 9) (1 / 2) GreenSchur_szF GreenSchur_zF inst_BAFlow
-- inst_row_l1 (statement lines 382-384)
  BAMB_row_l1 1 4 (by norm_num) g0P g0P (mS 4 10).im EP m0P g0P_pos g0P_pos le_rfl (selfS 4 10).1
    flowP_real a
-- inst_Mfine_eq (statement lines 389-392)
  have h := BAMfine_eq szP (fun _ => g0P) (fun _ => EP) 0 GreenSchur_hm 0 (fun _ => 1)
  rw [GreenSchur_mF] at h
  exact h
-- inst_Mfine_norm (statement lines 398-398)
  BAMfine_norm_le_one szP (fun _ => g0P) (fun _ => EP) 0 GreenSchur_hs x y
-- inst_Mfine_decay (statement lines 402-404)
  BAMfine_decay 3 (by norm_num) g0P (mS 4 10).im g0P_pos (selfS 4 10).1 szP (fun _ => g0P) (fun _ => EP) 0
    (by norm_num [szP]) g0P_pos le_rfl GreenSchur_hr x y
-- inst_Mfine_row_l1 (statement lines 409-411)
  BAMfine_row_l1 1 szP (fun _ => g0P) (fun _ => EP) 0 g0P (mS 4 10).im (by norm_num [szP]) g0P_pos g0P_pos
    le_rfl (selfS 4 10).1 GreenSchur_hr x
-- inst_Gt_sub_Mfine (statement lines 416-423)
  BAGt_sub_BAMfine szP (fun _ => g0P) (fun _ => EP) 0 (1 / 2) (fun _ => 1) (by norm_num) GreenSchur_hm
theorem inst_PsiI_inBlock : PsiI 3 4 2 (0 : Idx 3 4 2) (fun _ => 1) = 0 ∧
    (0 : Idx 3 4 2) ≠ (fun _ => 1) ∧ (split 3 4 2 (0 : Idx 3 4 2)).2 ≠ (split 3 4 2 (fun _ => 1 : Idx 3 4 2)).2 :=
  ⟨BAPsiI_inBlock 3 4 2 0 (fun _ => 1) (by decide), by decide, by decide⟩
-- inst_green_diag (statement lines 456-475)
  green_diag_split (id : Fin 2 → Fin 2) GreenSchur_D2 0 Complex.I GreenSchur_D2_hD (fun i k _ => rfl)
    GreenSchur_D2_hU 0 GreenSchur_D2_G00
-- inst_green_off (statement lines 480-488)
  green_off_split (id : Fin 2 → Fin 2) GreenSchur_D2 0 Complex.I GreenSchur_D2_hD (fun i k _ => rfl)
    GreenSchur_D2_hU 0 GreenSchur_D2_G00 ⟨1, by decide⟩
```
### Narrative (b)
- New file `RBM3D/BA/GreenSchur.lean`, 615 lines, imports exactly the six listed; 11 public theorems, one public def (`BAflowPert`, verbatim from the check file), 12 public instance theorems in `RBM.BA.GreenSchurInst`; every other helper is `private` with prefix `GreenSchur_`. No pin is proved or restated; the pre-check shows the same scanned-premise count with and without the module (153), so `RBM3D/Test/Axioms.lean` is untouched.
- Section (a) needed no correction; no (a′). The numeric check (viii) of the ticket is in (a) and was not rerun.
- Routes. T1: private `GreenSchur_zim_pos` (text of the private `ConArg_zim_pos`, `RBM3D/BA/ConArg.lean:1113`, not imported), `BAm_self`, `BAdom_real`, `BAm_real_eq_of_self`. T2: `BAFlow.1.2.2.2.2` (`WO`), `BAt0_pos`, `BAt0_lt_one`. T3: `BAMres_fine_apply`. T4: `BAMB_row_sq_real` plus T3. T5: `BAMB_decay_large` plus T3. T6: `Equiv.subLeft`, `sum_radial_exp_decay_le`. T7: fibre sum through `splitEquiv` (private `GreenSchur_fibre_sum`) plus T6. T8: units by `isUnit_sub_smul_of_isHermitian`, `A - B = BAflowPert` by `module`, then `Ring.inverse` algebra. T9: `PsiI`/`PsiV` entries, `PsiB d L a a = 0`. T10/T11: `green_diag_paper`/`green_off_diag_paper` plus `Finset.sum_filter_add_sum_filter_not` (private `GreenSchur_sum_split2`).
- The hypotheses `t < 1` and `0 < Im BAmF` of T8 enter only through the two unit facts; `A - B = BAflowPert` is proved for every real `t`.
- `import RBM3D.BA.ImmLower`: `BAm_im_lower` is not used (0 occurrences, script above). The import stays because the six listed imports reach `RBM.BA.CouplingWindowInst` (instances for T3-T9) only through it (compile of the file without it fails, script above).
- Instances (all 11 targets). T1, T2: `inst_BAFlow` is a genuine `BAFlow` at `L ≡ 4`, `W_n = n + 1`, `lam ≡ 1/100`, `z ≡ w - m_w`, `w = 11 i/10`, `κ = 9/10`, `ε = 1/2`, `𝔠 = 1/9`, `𝔡 = 1/2` (from `BASelf_subord`; `SizeTendsto`, `Bandwidth`, `WO` and `BAdom` proved, nothing left open); the ticket's I4 required none, and `inst_flow_real`/`inst_flow_window` apply T1/T2 to it. T3-T5, T7, T8: the one-point flow data of `CouplingWindow.lean` (`szP`, `g0P`, `EP`, `m0P`, `flowP_real`; T8 at `t = 1/2`, `ω ≡ 1`). T6: ticket I1. T9: ticket I2, with `0 ≠ (fun _ => 1)` and different offsets proved by `decide`. T10/T11: ticket I3 (`ι = β = Fin 2`, `b = id`, `X = 0`, `D = [[0,1],[1,0]]`, `z = i`; `det = -2` and `G_00 ≠ 0` proved by `Matrix.inv_def`/`adjugate_fin_two`).
- Not here (ticket): the a.s. block support of `seqXmat (sz.withLam 0)` (T10/T11 take the supports as hypotheses `hD`, `hX`), every LDE, `BAGbEXPii/ij/av`, the lattice-sum step of `(eq_resolventunderpoly)`. The preset cut T2296a/T2296b was not needed (615 lines).
## (c) Verified Mathlib names (script `names.lean`: `Lean.Environment.contains` after `import RBM3D.BA.GreenSchur`; every name is used in the file)
```
checked 39; present 38
Equiv.sum_comp Equiv.subLeft Fintype.sum_prod_type Finset.sum_filter_add_sum_filter_not 
Finset.sum_add_distrib Finset.single_le_sum Finset.mem_filter Finset.mul_sum 
Matrix.kroneckerMap_apply Matrix.submatrix_apply Matrix.add_apply Matrix.inv_def 
Matrix.adjugate_fin_two Matrix.det_fin_two Matrix.smul_apply Ring.inverse_mul_cancel 
Ring.mul_inverse_cancel Ring.inverse_eq_inv' Matrix.conjTranspose_smul Matrix.IsHermitian.add 
Complex.conj_ofReal Complex.norm_real Complex.norm_I Real.sqrt_pos 
Real.sqrt_le_one Real.rpow_pos_of_pos Real.rpow_natCast Real.rpow_mul 
Real.rpow_inv_le_iff_of_pos Real.rpow_le_rpow_of_nonpos Real.rpow_two Real.rpow_neg_one 
Filter.tendsto_atTop_mono tendsto_natCast_atTop_atTop Nat.le_self_pow Nat.pow_le_pow_left 
inv_anti₀ Filter.eventually_ge_atTop 
absent: [Real.rpow_le_rpow_of_exponent_nonpos]
```
Note: `Filter.tendsto_atTop_mono` is namespaced, `tendsto_natCast_atTop_atTop` is root; `Real.rpow_le_rpow_of_exponent_nonpos` does not exist, `Real.rpow_le_rpow_of_nonpos (hx : 0 < x) (hxy : x ≤ y) (hz : z ≤ 0) : y ^ z ≤ x ^ z` does.
## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none new. Differences already covered: T5 holds for every `0 < g₀ ≤ Λ` while `(Mbound_AO2)` (`7_8:1902`) is stated for `λ ≥ (2C)⁻¹` (BA-D4 = T2290, merged); T6, T7 are lattice-sum corollaries, not paper statements; T8 is stated and proved for every real `t < 1` (no `0 ≤ t`, ticket §29 (1)).
- Owed downstream (ticket): BA-G2 for the a.s. block support and the LDE of the in-block row; BA-G3...G6 as planned; plan-row update at merge (dispatcher).
- Registry: no `def … : Prop` added; the pre-check lists no new premise (counts above).
- `inst_BAFlow` (public, `RBM.BA.GreenSchurInst`) is a reusable nonvacuity witness of `BAFlow` at a growing sequence.
