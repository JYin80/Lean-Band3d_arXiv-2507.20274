Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 04:50:53 UTC 2026

### (i) Exponent table
Notation: `B = sz.Bctl n t`, `η = etaT E t = (1-t) Im m(E)`, `N = sz.size n`, `X_a = 𝓛^{(1)}_{+,a} - m`, `A = max_x |(G_t)_{xx}|`, `C` = the constant of target 1. `E_a = W^{-d} 1_{[a]}` (`Eblk`, GLoop:55-56), `Σ_b E_b = W^{-d} I`. All `≺` lose `N^τ` only.

| quantity | value / constraint | slack / evidence |
|---|---|---|
| `E, t` | `|E| < 2` (`st6_flowE_lt_two`), `0 ≤ t ≤ lemT z`, `t < 1` (`st5_t_lt_one`); `E, t` are the only data of targets 2, 5 | instance `E = 0.5`, `t = 1/16`, `lemT(z0 0) = 0.999991` (script 3) |
| `η` | `η ≤ 1` (`lwExpTerm_eta_le_one`), so `η⁻¹ ≥ 1`; `η⁻¹ ≤ N` eventually (`expAvg_eta_inv_le`) | `η = 0.90773`, `η⁻¹ = 1.1016 ≤ N = 2.1e6` |
| `B` | `B ≤ 1` (`st5_Bctl_le_one`), `N⁻¹ ≤ B` (`lwExpTerm_facts`); `B^{3} ≤ B^{5/2}` | `B = 3.305e-5`, `B^{1/2} = 5.7e-3`, `W³B = 1.083 → 16/15` |
| T1 `C` | `‖K_{ab}‖ ≤ C_K e^{-c|a-b|_∞}`; row sum `Σ_a ‖K_{ba}‖` is `Σ_x e^{-c|x|}` with `x = b-a`, column sum with `x = a-b`: one reindexing each, **no** `|-x| = |x|` needed. `C = C_K · S`, `S = Σ_{x∈Z_L^d} e^{-c|x|_∞}` | `d=3, c=1`: `S ≤ Σ_{Z³} = 49.979`; instance rows/cols `0.9478` vs `C_K S = 47.3` (script 2) |
| T1 **ticket's product bound is false** | `Σ e^{-c|x|_∞} ≤ (Σ_y e^{-c|y|})^d` fails: `|x|_∞ ≤ |x|_1` gives the reverse. Valid: `|x|_1 ≤ d|x|_∞` (`zdistD_le_mul_zdistInf`) so `e^{-c|x|_∞} ≤ e^{-(c/d)|x|_1}`, `Σ ≤ (Σ_y e^{-(c/d)|y|})^d` or `expC (d-2) (c/d)` (`sum_exp_decay_centre`) | `10.13 < 49.98` (false); `222.04 ≥ 49.98` (valid); Lean constant `expC 1 (1/3) = 497920` (script 2) |
| T1 `d` range | pin has no `3 ≤ d`; `sum_exp_decay_centre` needs `d = k+2`. `3 ≤ d` is **not needed**: for every `d`, `Zd d L ↪ Zd (d+2) L` (pad zeros) preserves `zdistD`; use `c/(d+1)` (`zdistD ≤ d·zdistInf ≤ (d+1)·zdistInf`) and `expC d (c/(d+1))` | `d = 0`: one point, `Σ_a‖K_{ab}‖ = ‖K_{00}‖ ≤ C` |
| T2 (`s = false`) | merged `lwExpTerm_ward_sum_le`, constant 1 | `ratio ≤ 0.986` (script 1) |
| T2 (`s = true`) | `D_a = W^{-d/2}1_{[a]}`, `X = D_a G D_b`, `Y = D_b G D_a`: `𝓛_{(+,+),(a,b)} = tr(XY)`, `‖X‖²_HS = 𝓛_{(-,+),(a,b)}`, `‖Y‖²_HS = 𝓛_{(-,+),(b,a)}`; so `|𝓛_{++,(a,b)}| ≤ ‖X‖_HS‖Y‖_HS ≤ ½(𝓛_{-+,(a,b)} + 𝓛_{-+,(b,a)})`. `Σ_b 𝓛_{-+,(a,b)} = W^{-d} tr(G G* E_a)`, `Σ_b 𝓛_{-+,(b,a)} = W^{-d} tr(G* G E_a)` (`Σ_b E_b = W^{-d}I`); `GG* = G*G = Im G/η` (`G` normal); both `= W^{-d} η⁻¹ Im 𝓛^{(1)}_{+,a}`. So `W^d Σ_b |𝓛_{++}| ≤ η⁻¹|𝓛^{(1)}_{+,a}|`, constant 1, only `|E|<2, t<1` | AM-GM ratio `≤ 0.9990`; T2 ratio at `s = true` `≤ 0.9620` (script 1; the `0.773` of T2243 is one sample) |
| T3 | `𝒦_{(s,+),(a,b)} = 𝒦_{(+,s),(b,a)}` (`KLK_rotate`, `σ = [true]`); `STKward` (`∀ σ : Fin k → Bool`), `k = 2`: `Σ_a ≺ (W^dη)⁻¹B^0`; `W^d × (W^dη)⁻¹ = η⁻¹` | slack 0; no sign condition on `s` |
| T4 | `‖G_xx‖ ≤ ‖m‖ + ‖STGM_{xx}‖`, `‖m‖ = 1` (`norm_mE`); `STLocalEntry` at `(x,x)`: `‖STGM‖² ≺ STWB(zdistInf 0) = STWB(0) = B ≤ 1`; the union over `x` is inside `P` (`badSetAt`: `∃ u`) | `‖STGM‖ ≺ B^{1/2} ≤ 1`; `A ≺ 1`, slack `B^{1/2} = 5.7e-3` |
| T5 | `Σ_a|𝓛^{(3)}_{(+,+,σ),(a,b,c)}| ≤ W^{-3d} Σ_{x∈[c],z∈[b]} |Ĝ_{zx}| Σ_y|G_{xy}||G_{yz}|`; `Σ_y|G_{xy}||G_{yz}| ≤ ((GG*)_{xx}(G*G)_{zz})^{1/2} = (Im G_xx Im G_zz)^{1/2}/η ≤ A/η`; `Σ_{x,z}|Ĝ_{zx}| ≤ W^d (Σ|Ĝ_{zx}|²)^{1/2} = W^{2d} 𝓛_{(-,+),(b,c)}^{1/2}` (`σ=+`; `(c,b)` for `σ=-`). So `W^d Σ_a ≤ η⁻¹ A (𝓛^{(2)}_{(-,+)})^{1/2}`, constant 1 | ratio `≤ 0.3382` (script 1) |
| `LWExpI1K` | `C(‖𝔼X‖‖𝒦^{(2)}‖ + ‖𝔼[X(𝓛-𝒦)^{(2)}]‖) ≤ C(B²·B + B³)`; `Σ_{a₁}|K_{a₁b}| ≤ C` replaces `Σ S = 1` | exponent `3 = 3`, slack 0; `Kenv = 4, Kf = 3` (`lwExpTerm_XD`) |
| `LWExpI23K` | `‖R‖ ≤ C (max|X|)² · W^dΣ_a|𝓛^{(3)}| ≤ C (N^τB)² η⁻¹ (N^τ)(N^τB)^{1/2}`: `2 + 1/2 = 5/2`; `sel = true`: `Σ_{a₁}|K_{a₁a₂}| ≤ C`, `Σ_{a₃}S_{a₂a₃} = 1`; `sel = false`: `Σ_{a₁}|K_{a₁a₂}| ≤ C`, then `Σ_{a₂}S_{a₂a₃} = 1` | slack 0 in `B`; envelope `‖R‖ ≤ C·4N²·N³ ≤ N⁶` (`A ≤ η⁻¹ ≤ N`, `‖𝓛^{(2)}‖ ≤ N²`), `Kenv = 6`; floor `η⁻¹B^{5/2} ≥ B^{5/2} ≥ N^{-5/2}`, `Kf = 5/2` |
| `LWExpI41K` | `T_a`: `B·B²·η⁻¹·1` (T2, `‖𝓛^{(1)}‖ ≺ 1`); `T_{b1}`: `B²·B·η⁻¹` (`‖𝒦^{(2)}_{(s,+)}‖ ≺ B` any charge, T3); `T_{b2}`: `B³·η⁻¹`; sums `Σ_{a₁}|K_{a₁a₂}| ≤ C`, `Σ S = 1` | exponent `3 = 3`, slack 0; `Kenv = 6` (`C·4N⁵ ≤ N⁶`), `Kf = 3` |
| constants | `C ≤ N^{τ/3}` and `4C ≤ N` eventually (`N → ∞`, `SizeTendsto`) | `4 C_K S = 189.5 ≤ N = 2.1e6` (script 3) |

### (ii) One concrete nondegenerate instance
Targets 6-9 (`LWExpI1K, I23K, I41K`, `lwCutExp_of_G5'`): `d = 3`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`), `z0 n = 1/2 + i N^{-4/5}`, `t = tInst = 1/16`, `K = lwExpTerm2_KK` (`LWExpKer`, `C_K = 0.948`, `c = 1`, script 2). `STFlow` is merged (`flow_z0`). The five ST laws stay hypotheses (other gates' pins). Limit computation for them at `tInst`: `W³B = (lam² + 1-t)⁻¹ + (L³(1-t))⁻¹ → 1/(1-t) = 16/15`, so `B ~ (16/15)W^{-3} → 0`, `N B ≥ L³ → ∞` (`B ≥ N⁻¹`), every bound `η⁻¹B^{5/2}, η⁻¹B³, B³` is positive and tends to `0` (script 3). Targets 1-3: `K` as above, `n = 0, 1, 2`. Targets 2, 5 (pathwise, any Hermitian `H`, `Im z > 0`): `E = lemE(z0 0) = 0.5`, `t = 1/16`, `η = 0.90773` of the `n = 0` instance; the matrix check uses the lattice `d = 3, L = 3, W = 2` (`N = 216`), since `N = 2 097 152` at `n = 0` is too large (the inequalities are dimension-free). Target 4: `STLocalEntry` is a hypothesis; `B = 3.3e-5 ≤ 1`, `‖m‖ = 1` hold.
```
$ cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2254 && sh run.sh      # run.sh = python3 num.py; python3 ker2.py; python3 pre2.py   (script 1 = num.py, 2 = ker2.py, 3 = pre2.py)
E0=lemE(z0 0)=0.500000 t=1/16 |E|<2:True t<1:True |m|=1.000000000000000 eta=etaT=0.907730 (1-t)^-1/eta=1.1751 eta^-1=1.1016
band lam=0.5 #0 [instance eta]  eta=0.9077  AMGM max=0.9673  T2[s=0] max LHS/RHS=0.9757  T2[s=1] max LHS/RHS=0.9399  T5[sigma=+] max LHS/RHS=0.3111 (sharp pair bound 0.3111)  T5[sigma=-] max LHS/RHS=0.3333 (sharp pair bound 0.3333)
band lam=0.5 #1 [instance eta]  eta=0.9077  AMGM max=0.9658  T2[s=0] max LHS/RHS=0.9783  T2[s=1] max LHS/RHS=0.9371  T5[sigma=+] max LHS/RHS=0.3063 (sharp pair bound 0.3063)  T5[sigma=-] max LHS/RHS=0.3311 (sharp pair bound 0.3311)
band lam=0.01562 #0 [instance eta]  eta=0.9077  AMGM max=0.9211  T2[s=0] max LHS/RHS=0.9780  T2[s=1] max LHS/RHS=0.8925  T5[sigma=+] max LHS/RHS=0.2697 (sharp pair bound 0.2700)  T5[sigma=-] max LHS/RHS=0.3174 (sharp pair bound 0.3177)
band lam=0.01562 #1 [instance eta]  eta=0.9077  AMGM max=0.9185  T2[s=0] max LHS/RHS=0.9857  T2[s=1] max LHS/RHS=0.8893  T5[sigma=+] max LHS/RHS=0.2716 (sharp pair bound 0.2731)  T5[sigma=-] max LHS/RHS=0.3255 (sharp pair bound 0.3255)
dense lam=0 #0 [instance eta]  eta=0.9077  AMGM max=0.9973  T2[s=0] max LHS/RHS=0.9711  T2[s=1] max LHS/RHS=0.9618  T5[sigma=+] max LHS/RHS=0.3350 (sharp pair bound 0.3350)  T5[sigma=-] max LHS/RHS=0.3370 (sharp pair bound 0.3370)
dense lam=0 #1 [instance eta]  eta=0.9077  AMGM max=0.9972  T2[s=0] max LHS/RHS=0.9710  T2[s=1] max LHS/RHS=0.9620  T5[sigma=+] max LHS/RHS=0.3357 (sharp pair bound 0.3360)  T5[sigma=-] max LHS/RHS=0.3382 (sharp pair bound 0.3382)
band lam=0.5 #0 [eta=0.05]  eta=0.05  AMGM max=0.9790  T2[s=0] max LHS/RHS=0.6257  T2[s=1] max LHS/RHS=0.3507  T5[sigma=+] max LHS/RHS=0.1323 (sharp pair bound 0.1432)  T5[sigma=-] max LHS/RHS=0.1582 (sharp pair bound 0.1712)
band lam=0.5 #0 [eta=0.005]  eta=0.005  AMGM max=0.9990  T2[s=0] max LHS/RHS=0.2936  T2[s=1] max LHS/RHS=0.2845  T5[sigma=+] max LHS/RHS=0.1614 (sharp pair bound 0.1614)  T5[sigma=-] max LHS/RHS=0.1617 (sharp pair bound 0.1617)
c=1,d=3: sum_(Z^3) e^(-|x|_inf) = 49.9790;  (sum_(Z) e^(-|y|))^3 = 10.1331  -> product bound with |x|_inf FALSE (10.13 < 49.98);
         zdistD route: sum_(Z^3) e^(-(c/d)|x|_1) = (sum_Z e^(-(c/d)|y|))^3 = 222.04 >= 49.98 (valid, since |x|_1 <= d|x|_inf)
Lean route constant expC k=1 (c/d=0.3333) = 2^(k+2)*2*2^(k+3)*(1+(k+3)!/(c/d)^(k+3)) = 497920 (uniform in L; crude, finite)
n   L    N        E         eta     eta^-1  Bctl      W^3*B   B<=1  N^-5/2<=B^5/2  eta^-1 B^5/2   B^1/2    max|K|e^|a-b| rowsum(K) colsum(K)  bound C_K*49.98
0 4 2.097e+06 0.500000 0.90773 1.1016 3.305e-05 1.0831 True True 6.919e-12 5.749e-03 0.9464 0.9478 0.9478 47.302
1 8 5.498e+11 0.500000 0.90773 1.1016 9.954e-10 1.0687 True True 3.443e-23 3.155e-05 0.9478 0.9478 0.9478 47.368
2 12 8.125e+14 0.500000 0.90773 1.1016 2.270e-12 1.0673 True True 8.552e-30 1.507e-06 0.9478 0.9478 0.9478 47.368
n  N  |E|<=2-k  t<=lemT(z)  t<1  eta^-1<=N  B<=1  N^-1<=B  4*C_K*49.98<=N  W^3*B  B^(1/2)  eta^-1*B^(5/2)  [lemT, E]
0 2.097e+6 True True True True True True True 1.08306 0.005749 6.919e-12 [0.999991, 0.5]
1 5.498e+11 True True True True True True True 1.06875 3.155e-5 3.443e-23 [1.0, 0.5]
2 8.125e+14 True True True True True True True 1.06728 1.507e-6 8.552e-30 [1.0, 0.5]
5 2.13e+20 True True True True True True True 1.06674 8.321e-9 4.394e-41 [1.0, 0.5]
50 1.143e+37 True True True True True True True 1.06667 8.903e-16 6.16e-76 [1.0, 0.5]
limit n->inf at tInst: W^3*B -> 1/(1-t) = 16/15 = 1.0666667 ; B ~ (16/15) W^-3 -> 0; N^-1 <= B since W^3 L^3 B -> inf
```
(In script 1 the `AMGM` entry is `max |𝓛_{(+,+),(u,v)}| / (½(𝓛_{(-,+),(u,v)} + 𝓛_{(-,+),(v,u)}))`; `T2`/`T5` entries are the max over all `a` resp. `(b,c)` of LHS/RHS of the pins with `RHS = η⁻¹|𝓛^{(1)}_{+,a}|` resp. `η⁻¹ A √(max 𝓛^{(2)}_{(-,+)})`; `num.py` asserts the einsum loops equal the direct matrix traces.)

### Verdicts
- Target 1 `lwExpTerm4_kerSum`: PASS (true for all `d`; the ticket's product shortcut with `|x|_∞` is false, use `zdistD ≤ d·zdistInf`; no `3 ≤ d` needed, see row "T1 `d` range").
- Target 2 `lwExpTerm4_ward2`: PASS (`s = true` by Hilbert-Schmidt Cauchy-Schwarz, constant 1).  Target 3 `lwExpTerm4_kward`: PASS.  Target 4 `lwExpTerm4_diag`: PASS.  Target 5 `lwExpTerm4_L3`: PASS.
- Targets 6, 7, 8 (`LWExpI1K`, `LWExpI23K`, `LWExpI41K`, both `s`): PASS; no merged pin is false as stated; the rest of `lwExpI41_holds` is charge-blind (T_a, T_{b1}, T_{b2} use only `STKbound`, `STLK`, `STExpAvgAt`, T2, T3).  Target 9 `lwCutExp_of_G5'`: PASS (one line from 6-8).  Target 10 (instances): PASS.
- Size estimate: not given (stage-1a rule); extra work beyond the ticket's list: `d ≤ 1` padding in target 1, the fine-to-block bridge `𝓛^{(3)} = Σ_{x,y,z}` in target 5.
- §29: (1) `0≤t≤lemT z`, `t<1` as in table; (2) no `ĝ²/L^d ≤ 1-t` in targets 1-8; (3) no `L^d ≤ W^K`; (4) `C` of target 1 uniform in `n, L`; (5) deterministic left sides, uniform index; (6) `0 < lam` unused; (7) scale `N`, control `sz.Bctl n (t n)`.

## (b) Script output -- Tue Oct  6 05:19:57 UTC 2026

Branch `t/T2254`, worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2254`, HEAD `cdf2967977c1eb6773b3b2d68897d1cbe7b41651`, new file `RBM3D/Graph/LWExpTerm4.lean` (1838 lines).
```
$ lake build RBM3D.Graph.LWExpTerm4          # exit 0
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3857 jobs).
$ grep -cE '\b(sorry|admit|native_decide)\b|^axiom ' RBM3D/Graph/LWExpTerm4.lean
0
$ grep -nE '^(def|abbrev|structure|class|inductive) ' RBM3D/Graph/LWExpTerm4.lean | head     # Prop-valued defs: none; non-private defs: none
(no output)
$ git diff --stat main...t/T2254
 RBM3D/Graph/LWExpTerm4.lean | 1838 +++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean      |    3 -
 2 files changed, 1838 insertions(+), 3 deletions(-)
$ git diff main...t/T2254 -- RBM3D/Test/Axioms.lean | grep '^[-+] '      # registry: the three owed lines of LW-14d
-   `RBM.Gauss.Sizes.LWExpI1K, -- `I₁`, `J₁` (`(eq:termI1)`, `B:37-41`
-   `RBM.Gauss.Sizes.LWExpI23K, -- `I₂`, `I₃`, `J₂`, `J₃` (`(eq:termI2
-   `RBM.Gauss.Sizes.LWExpI41K, -- `I₄₁`, `J₄₁` (`(eq:termI41)`, `B:57
```
Full build, as the hub runs it at merge: temporary line `import RBM3D.Graph.LWExpTerm4` after the last import of `RBM3D.lean`, then `git checkout RBM3D.lean` (the root import is the hub's). Without that line the full build stops at `#assert_rbm_axioms` on the 3 premises `LWExpI1K, LWExpI23K, LWExpI41K` (deleted from `owedProps`, not yet proved in the library): merge the root import with the registry hunk.
```
$ lake build        # temporary root import; exit 0
3011:info: RBM3D.lean:298:0: axiom audit: 7521 theorems, 2530 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
3297:Build completed successfully (4058 jobs).
$ lake env lean precheck.lean      # = `import RBM3D` + `import RBM3D.Graph.LWExpTerm4` + `#assert_rbm_axioms`; exit 0
axiom audit: 7521 theorems, 2530 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ grep -c 'LWExpI1K|LWExpI23K|LWExpI41K' precheck.out      # in the owed list after the deletion
0
```
(`RBM3D.olean` of this worktree was built with the temporary import, so `import RBM3D` there already contains the new module; the audit result is the post-merge one.)

Axioms (`lake env lean axioms4.lean`, exit 0):
```
'Sizes.lwExpI1K_holds' : [propext, Classical.choice, Quot.sound]
'Sizes.lwExpI23K_holds' : [propext, Classical.choice, Quot.sound]
'Sizes.lwExpI41K_holds' : [propext, Classical.choice, Quot.sound]
'Sizes.lwCutExp_of_G5'' : [propext, Classical.choice, Quot.sound]
'Sizes.lwExpTerm4_kerSum' : [propext, Classical.choice, Quot.sound]
'Sizes.lwExpTerm4_ward2' : [propext, Classical.choice, Quot.sound]
'Sizes.lwExpTerm4_kward' : [propext, Classical.choice, Quot.sound]
'Sizes.lwExpTerm4_diag' : [propext, Classical.choice, Quot.sound]
'Sizes.lwExpTerm4_L3' : [propext, Classical.choice, Quot.sound]
'LWInst.lwExpTerm4_inst_cut' : [propext, Classical.choice, Quot.sound]
'LWInst.lwExpTerm4_inst_I1K' : [propext, Classical.choice, Quot.sound]
'LWInst.lwExpTerm4_inst_I23K' : [propext, Classical.choice, Quot.sound]
'LWInst.lwExpTerm4_inst_I41K' : [propext, Classical.choice, Quot.sound]
'LWInst.lwExpTerm4_inst_kerSum' : [propext, Classical.choice, Quot.sound]
'LWInst.lwExpTerm4_inst_ward2' : [propext, Classical.choice, Quot.sound]
'LWInst.lwExpTerm4_inst_L3' : [propext, Classical.choice, Quot.sound]
'LWInst.lwExpTerm4_inst_L3_full' : [propext, Classical.choice, Quot.sound]
'LWInst.lwExpTerm4_inst_kward' : [propext, Classical.choice, Quot.sound]
'LWInst.lwExpTerm4_inst_diag' : [propext, Classical.choice, Quot.sound]
```
Pins accepted (`check4.lean` = section 2 of `docs/tickets/checks/T2254-check.lean` copied verbatim by script into a scratch namespace, plus these term-mode examples; `lake env lean`, exit 0, no output):
```
example : ∀ d, LWExpI1K d := @lwExpI1K_holds
example : ∀ d, LWExpI23K d := @lwExpI23K_holds
example : ∀ d, LWExpI41K d := @lwExpI41K_holds
example : ∀ d, T2254Check.LwCutExpOfG5'Pin d := @lwCutExp_of_G5'
example : T2254Check.LwExpTerm4KerSumPin :=
  fun d sz K hK => lwExpTerm4_kerSum d sz K hK
example : T2254Check.LwExpTerm4WardPin :=
  fun d sz n E t hE ht s a ω => lwExpTerm4_ward2 d sz n E t hE ht s a ω
example : ∀ d, T2254Check.LwExpTerm4KwardPin d := fun d => lwExpTerm4_kward d
example : ∀ d, T2254Check.LwExpTerm4DiagPin d := fun d => lwExpTerm4_diag d
example : T2254Check.LwExpTerm4L3Pin :=
  fun d sz n E t hE ht σ b c ω A hA => lwExpTerm4_L3 d sz n E t hE ht σ b c ω A hA
```
Targets, statements extracted from the file by script (`line: text`; targets 6-9 are the merged pins `LWExpI1K`, `LWExpI23K`, `LWExpI41K` at `LWExpTerm2.lean:81,96,115`):
```
100: theorem lwExpTerm4_kerSum (d : ℕ) (sz : Sizes d) (K : ∀ n, Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ)
    (hK : LWExpKer sz K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (b : Zd d (sz.L n)),
      ∑ a : Zd d (sz.L n), ‖K n a b‖ ≤ C ∧ ∑ a : Zd d (sz.L n), ‖K n b a‖ ≤ C
391: theorem lwExpTerm4_ward2 (d : ℕ) (sz : Sizes d) (n : ℕ) (E t : ℝ) (hE : |E| < 2) (ht : t < 1)
    (s : Bool) (a : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    (((sz.W n : ℕ) : ℝ) ^ d) * ∑ b : Zd d (sz.L n), ‖Lloop sz n E t ![s, true] ![a, b] ω‖ ≤
      (etaT E t)⁻¹ * ‖Lloop sz n E t ![true] ![a] ω‖
488: theorem lwExpTerm4_L3 (d : ℕ) (sz : Sizes d) (n : ℕ) (E t : ℝ) (hE : |E| < 2) (ht : t < 1)
    (σ : Bool) (b c : Zd d (sz.L n)) (ω : sz.SeqΩ) (A : ℝ)
    (hA : ∀ x : Idx d (sz.L n) (sz.W n), ‖Gt sz n E t true ω x x‖ ≤ A) :
    (((sz.W n : ℕ) : ℝ) ^ d) * ∑ a : Zd d (sz.L n), ‖Lloop sz n E t ![true, true, σ] ![a, b, c] ω‖ ≤
      (etaT E t)⁻¹ * A * Real.sqrt (STmaxLoop2 sz n E t ω)
746: theorem lwExpTerm4_kward (d : ℕ) : 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        Prec sz (U := fun n => Bool × Zd d (sz.L n))
          (fun n p _ => (((sz.W n : ℕ) : ℝ) ^ d) * ∑ a : Zd d (sz.L n),
              ‖STKloop sz n (STflowE z n) (t n) ![p.1, true] ![a, p.2]‖)
          (fun n _ _ => (etaT (STflowE z n) (t n))⁻¹)
781: theorem lwExpTerm4_diag (d : ℕ) : 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        STLocalEntry sz (STflowE z) t →
        Prec sz (U := fun n => Idx d (sz.L n) (sz.W n))
          (fun n x ω => ‖Gt sz n (STflowE z n) (t n) true ω x x‖)
          (fun _ _ _ => 1)
903: theorem lwExpI1K_holds (d : ℕ) : LWExpI1K d
1316: theorem lwExpI23K_holds (d : ℕ) : LWExpI23K d
1618: theorem lwExpI41K_holds (d : ℕ) : LWExpI41K d
1717: theorem lwCutExp_of_G5' (d : ℕ) : LWExpG5' d → LWCutExp d
```
Compiled nonempty instances (`namespace RBM.Gauss.LWInst`, `d = 3`, `sz0` (`sz0_values`: `L 0 = 4`, `W 0 = 32`, `size 0 = 2097152`), `z0`, `flow_z0`, `tInst`; `file lines: first line of the statement`, then the proof term; `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`; every deterministic hypothesis (`3 ≤ 3`, `0 < 1/10`, `flow_z0`, `0 ≤ tInst`, `tInst ≤ lemT z0`, `|E| < 2`, `t < 1`, `LWExpKer` of `lwExpTerm2_KK`) is discharged; remaining hypotheses are the five ST laws and `LWExpG5' 3`, i.e. other gates' pins, and in `inst_L3` the bound `A`):
```
1733-1740 theorem lwExpTerm4_inst_cut (h5 : LWExpG5' 3) (h1 : STLocalEntry sz0 (STflowE z0) tInst)
  inst_LWtermEXP (lwTermEXP_of_cut 3 (lwCutExp_of_G5' 3 h5)) h1 h2 h3 h4 h5'
1743-1751 theorem lwExpTerm4_inst_I1K (hLW : LWAvgLaw sz0 (STflowE z0) tInst) (hLK : STLK sz0 (STflowE z0) tInst) :
  lwExpI1K_holds 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    sz0 z0 flow_z0 tInst tInst_range.1 tInst_range.2 (fun n => lwExpTerm2_KK sz0 n (STflowE z0 n) (tInst n))
    lwExpTerm2_inst_ker_KK hLW hLK
1754-1768 theorem lwExpTerm4_inst_I23K (hLE : STLocalEntry sz0 (STflowE z0) tInst) (hLW : LWAvgLaw sz0 (STflowE z0) tInst)
  lwExpI23K_holds 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    sz0 z0 flow_z0 tInst tInst_range.1 tInst_range.2 (fun n => lwExpTerm2_KK sz0 n (STflowE z0 n) (tInst n))
    lwExpTerm2_inst_ker_KK hLE hLW hLmax hLK hDec
1771-1782 theorem lwExpTerm4_inst_I41K (hLW : LWAvgLaw sz0 (STflowE z0) tInst) (hLmax : STLmax sz0 (STflowE z0) tInst)
  lwExpI41K_holds 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    sz0 z0 flow_z0 tInst tInst_range.1 tInst_range.2 (fun n => lwExpTerm2_KK sz0 n (STflowE z0 n) (tInst n))
    lwExpTerm2_inst_ker_KK hLW hLmax hLK
1785-1789 theorem lwExpTerm4_inst_kerSum :
  lwExpTerm4_kerSum 3 sz0 (fun n => lwExpTerm2_KK sz0 n (STflowE z0 n) (tInst n)) lwExpTerm2_inst_ker_KK
1793-1799 theorem lwExpTerm4_inst_ward2 (s : Bool) (a : Zd 3 (sz0.L 0)) (ω : sz0.SeqΩ) :
  lwExpTerm4_ward2 3 sz0 0 (STflowE z0 0) (tInst 0)
    (st6_flowE_lt_two sz0 (by norm_num : (0 : ℝ) < 1 / 10) flow_z0 0) (st5_t_lt_one sz0 flow_z0 tInst_range.2 0)
    s a ω
1803-1810 theorem lwExpTerm4_inst_L3 (σ : Bool) (b c : Zd 3 (sz0.L 0)) (ω : sz0.SeqΩ) (A : ℝ)
  lwExpTerm4_L3 3 sz0 0 (STflowE z0 0) (tInst 0)
    (st6_flowE_lt_two sz0 (by norm_num : (0 : ℝ) < 1 / 10) flow_z0 0) (st5_t_lt_one sz0 flow_z0 tInst_range.2 0)
    σ b c ω A hA
1813-1820 theorem lwExpTerm4_inst_L3_full (σ : Bool) (b c : Zd 3 (sz0.L 0)) (ω : sz0.SeqΩ) :
  lwExpTerm4_inst_L3 σ b c ω _ fun x =>
    lwExpTerm4_Gt_entry_le sz0 0 (st6_flowE_lt_two sz0 (by norm_num : (0 : ℝ) < 1 / 10) flow_z0 0)
      (st5_t_lt_one sz0 flow_z0 tInst_range.2 0) ω x
1823-1829 theorem lwExpTerm4_inst_kward :
  lwExpTerm4_kward 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    sz0 z0 flow_z0 tInst tInst_range.1 tInst_range.2
1832-1836 theorem lwExpTerm4_inst_diag (hLE : STLocalEntry sz0 (STflowE z0) tInst) :
  lwExpTerm4_diag 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    sz0 z0 flow_z0 tInst tInst_range.1 tInst_range.2 hLE
```
Name clash (new public names `lwExpTerm4_*`, `lwExpI1K_holds`, `lwExpI23K_holds`, `lwExpI41K_holds`, `lwCutExp_of_G5'`):
```
$ grep -rnE "lwExpTerm4_|lwExpI1K_holds|lwExpI23K_holds|lwExpI41K_holds|lwCutExp_of_G5'" RBM3D | grep -v Graph/LWExpTerm4.lean | wc -l      # worktree
0
$ (same grep in the main worktree RBM3D/)
0
$ grep -rlE "lwExpTerm4_|lwExpI1K_holds|lwExpI23K_holds|lwExpI41K_holds|lwCutExp_of_G5'|LWExpTerm4" docs/tickets      # main worktree: ticket texts (plans), no Lean
docs/tickets/T2243.md docs/tickets/T2254.md docs/tickets/T2255.md docs/tickets/T2257.md docs/tickets/T2258.md docs/tickets/T2259.md
```
Ports: none (ticket: "No port"); no file of `../RBM1D` or `../RBM2D` was read or run, so no `git diff --stat` against them.  Private helpers of `LWExpTerm.lean` (T2236), not importable, are copied with `lwExpTerm_` -> `lwExpTerm4_` by script from `LWExpTerm.lean:196-203` (`prec_congr`), `:336-457` (`vec1`, `Kloop_one`, `facts`, `env_X/L2/D`, `floor3`, `XD`), `:466-495` (`int_X`, `int_XL`), `:849-872` (`int_split3`), by hand `:996-1005` (`eta_le_one`, here `lwExpTerm4_eta_le_one`); adapted to a kernel `K` (column sums `<= C`): `:498` `I1_n` -> `I1K_n`, `:792` `Ta_n`, `:819` `Tb_n`, `:886` `I41_split` -> `I41K_split`, `:914-1075` `Ra`, `Ra_prec`, `Ta_det`, `:1077` `Kward` -> target 3 (all charges); new: `T23_n`, `wsum2K`, `wsum3K`, `int_sum3`, `prec_union3`.  The BM lemmas are the public `lwExpTerm2_BM_*`.  Counts in the file: 64 private declarations, 19 public theorems (9 targets, 10 instances).
Narrative
- Targets 1-5 are proved as theorems with the statements of the check file's section 2 (accepted by the term-mode examples above); targets 6-9 close the merged pins as stated, both charges, for every `LWExpKer` kernel, with no extra hypothesis.
- Target 1: `|x|_1 <= d |x|_inf <= (d+1) |x|_inf`, padding `Z_L^d -> Z_L^(d+2)` (`Fin.append`, zdistD unchanged), `sum_radial_exp_decay_le`: `C = C_K expC d (c/(d+1))`, uniform in `n, L`, every `d` (no `3 <= d`); row sum by `a -> b - a`, column sum by `a -> a - b` (`Equiv.subLeft/subRight`).  The ticket's product shortcut is not used (see (a), row "T1 ticket's product bound is false").
- Fine Ward (`lwExpTerm4_ward_row/col`): from `RBM.green_sub_green`, `RBM.green_sub_green_conj'` and `green (z̄) = (green z)ᴴ`: `Im z * Σ_y |G_xy|² = Im G_xx = Im z * Σ_y |G_yx|²`.
- Target 2: with `P(a,b) = Σ_{x,y} |G_yx|² ρ_a(y) ρ_b(x)`: `𝓛_(-,+),(a,b) = P(a,b)` (`lwExpTerm2_Lloop2`, `lwExpTerm2_conj_Gt`), `|𝓛_(+,+),(a,b)| <= (P(a,b)+P(b,a))/2` entrywise (AM-GM), and `W^d Σ_b P(a,b) = W^d Σ_b P(b,a) = η⁻¹ Im 𝓛^(1)_(+,a)` (row and column Ward); no operator-norm or Hilbert-Schmidt API needed.
- Target 5: `lwExpTerm2_Lloop3`, `Σ_a ρ_a = W^-d`, vertex bound `Σ_y |G_xy||G_yz| <= A/η` (Cauchy-Schwarz + fine Ward), weighted Cauchy-Schwarz over the pairs `(z,x)` with weights `ρ_b(z)ρ_c(x)` summing to 1, and `Σ ρ_b ρ_c |Ĝ_zx|² = P(b,c)` or `P(c,b)` `<= STmaxLoop2`.
- Target 3: `stKward_of_flow` at `![true, s]` and `KLK_rotate` with `σ = [true]`, `s` arbitrary.  Target 4: the failure event of `‖G_xx‖ > N^τ` lies inside that of `‖STGM‖² > N^τ B` at `(x,x)` (`N^τ >= 4`, `B <= 1`, `‖m‖ = 1`); proved directly from `StochDomAt` because `StochDomAt.of_subset` needs one index type.
- Targets 6-8 follow `lwExpI1_holds`/`lwExpI41_holds` with `Σ_a1 ‖S‖ = 1` replaced by `Σ_a1 ‖K_(a1,b)‖ <= C`; the constant `C` is absorbed by `N^(τ/3) >= 2C+2` (T6), `N^(τ/5) >= C+1` (T7), `N^(τ/3) >= C` and `N^(τ/4) >= C+2` (T8).
- Target 7: `∫` through the sums (`lwExpTerm4_int_R23`), `‖R‖ <= C M² η⁻¹ A √(STmaxLoop2)` pathwise (`lwExpTerm4_R23_le`), good event of three laws (`STLK k=1`, target 4, `STLmax k=2`) via the new `lwExpTerm4_prec_union3` (copy of `of_subset_union` with three events), `‖R‖ <= u⁵ η⁻¹ B² √B`, `B^(5/2) = B² √B`; then `lwExpTerm_prec_integral` with `Kenv = 7` (`‖R‖ <= 4C N⁶ <= N⁷`; crude card bound, `(a)` planned `Kenv = 6`), `Kf = 5/2`.  Target 8: `Kenv = 6`, `Kf = 3` for `T_a`; the Ward steps are targets 2 (second label of `(s,+)`) and 3 (first label).
- The `s = true` cases of `LWExpI41K` hold: the only `s`-dependent steps are targets 2 and 3.  No merged pin was found false.

## (c) Verified names (`#check`, `names.lean`, exit 0; first line of each signature)
```
Finset.sum_mul_sq_le_sq_mul_sq : ∀ {ι : Type u_1} {R : Type u_2} [inst : CommSemiring R] [inst_1 : LinearOrder
Real.le_sqrt_of_sq_le : ∀ {x y : ℝ}, x ^ 2 ≤ y → x ≤ √y
sq_le_sq₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : LinearOrder M₀] [PosMulStrictMono M₀] {a b 
Real.sqrt_le_iff : ∀ {x y : ℝ}, √x ≤ y ↔ 0 ≤ y ∧ x ≤ y ^ 2
Real.sqrt_le_sqrt : ∀ {x y : ℝ}, x ≤ y → √x ≤ √y
Real.sqrt_mul : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), √(x * y) = √x * √y
Real.sqrt_eq_rpow : ∀ (x : ℝ), √x = x ^ (1 / 2)
Fin.append : {m n : ℕ} → {α : Sort u_1} → (Fin m → α) → (Fin n → α) → Fin (m + n) → α
Fin.append_left : ∀ {m n : ℕ} {α : Sort u_1} (u : Fin m → α) (v : Fin n → α) (i : Fin m),
Fin.sum_univ_add : ∀ {M : Type u_1} [inst : AddCommMonoid M] {a b : ℕ} (f : Fin (a + b) → M),
Finset.sum_image : ∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : AddCommMonoid M] {f : ι → M}
Finset.sum_le_sum_of_subset_of_nonneg : ∀ {ι : Type u_1} {N : Type u_2} [inst : AddCommMonoid N] [inst_1 : Pre
Fintype.sum_equiv : ∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : Fintype ι] [inst_1 : Fintype κ]
Equiv.subLeft : {G : Type u_1} → [AddGroup G] → G → G ≃ G
Equiv.subRight : {G : Type u_1} → [AddGroup G] → G → G ≃ G
Complex.conj_mul' : ∀ (z : ℂ), (starRingEnd ℂ) z * z = ↑‖z‖ ^ 2
Complex.sub_conj : ∀ (z : ℂ), z - (starRingEnd ℂ) z = ↑(2 * z.im) * Complex.I
Complex.im_le_norm : ∀ (z : ℂ), z.im ≤ ‖z‖
Complex.im_sum : ∀ {α : Type u_1} (s : Finset α) (f : α → ℂ), (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im
Complex.im_mul_ofReal : ∀ (z : ℂ) (r : ℝ), (z * ↑r).im = z.im * r
Complex.norm_real : ∀ (r : ℝ), ‖↑r‖ = ‖r‖
pow_lt_pow_left₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : PartialOrder M₀] {a b : M₀}
Finset.le_sup' : ∀ {α : Type u_1} {β : Type u_2} [inst : SemilatticeSup α] {s : Finset β} (f : β → α) {b : β}
Finset.sup'_le : ∀ {α : Type u_1} {β : Type u_2} [inst : SemilatticeSup α] {s : Finset β} (H : s.Nonempty) (f 
Fintype.sum_prod_type : ∀ {γ : Type u_1} {α₁ : Type u_2} {α₂ : Type u_3} [inst : Fintype α₁] [inst_1 : Fintype
Finset.single_le_sum : ∀ {ι : Type u_1} {N : Type u_2} [inst : AddCommMonoid N] [inst_1 : Preorder N] {f : ι →
le_mul_inv_iff₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [MulPosReflectLT G₀]
one_le_inv₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] {a :
Real.inv_rpow : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), x⁻¹ ^ y = (x ^ y)⁻¹
Real.rpow_neg : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), x ^ (-y) = (x ^ y)⁻¹
Real.rpow_natCast : ∀ (x : ℝ) (n : ℕ), x ^ ↑n = x ^ n
ENNReal.ofReal_add : ∀ {p q : ℝ}, 0 ≤ p → 0 ≤ q → ENNReal.ofReal (p + q) = ENNReal.ofReal p + ENNReal.ofReal q
measure_union_le : ∀ {α : Type u_1} {F : Type u_2} [inst : FunLike F (Set α) ENNReal] [OuterMeasureClass F α] 
integral_finsetSum : ∀ {α : Type u_1} {G : Type u_2} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G]
Matrix.conjTranspose_nonsing_inv : ∀ {n : Type u_1} {α : Type u_2} [inst : Fintype n] [inst_1 : DecidableEq n]
Real.mul_self_sqrt : ∀ {x : ℝ}, 0 ≤ x → √x * √x = x
Real.sq_sqrt : ∀ {x : ℝ}, 0 ≤ x → √x ^ 2 = x
```
Project name `sum_exp_decay_centre` (`PureLoop:144`) is not used: target 1 uses `sum_radial_exp_decay_le` (`Defs/RadialSum`) after padding.  Project names used and compiled: `RBM.green_sub_green`, `RBM.green_sub_green_conj'`, `RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero`, `RBM.Ind.Gres_eq_green_zSig`, `RBM.sum_radial_exp_decay_le`, `RBM.expC`, `lwExpTerm2_Lloop1/2/3`, `lwExpTerm2_conj_Gt`, `lwExpTerm2_BM_*`, `lwExpTerm2_hc`, `lwExpTerm2_dw_sum`, `lwExpTerm_prec_integral`.

## (d) Open issues and paper-delta candidates
- Open: none for the targets.  The instances keep `LWExpG5' 3`, `LWAvgLaw`, `STLK`, `STLmax`, `STLocalEntry`, `STDecay` as hypotheses (other gates' pins; LW-14c, LW-12/KL/ST gates).  `lwExpTerm4_inst_L3_full` has no hypothesis at all (`A = η⁻¹` by `lwExpTerm4_Gt_entry_le`).
- Size: 1838 lines against the ticket estimate 1300-1500 (informational).
- Hub: the registry hunk (delete 3 owed lines) and the root import must go in together (see the full-build note in (b)); `RBM3D/Test/Axioms.lean` on `main` differs from the branch point (merge-base `24b85cd`) by 1 inserted line (`8aa37bf`, T2252), so apply the 3-line deletion by text.
- Ticket note (not a paper statement): the product bound `Σ e^(-c|x|_inf) <= (Σ_y e^(-c|y|))^d` of target 1 is false; (a) records numbers (`10.13 < 49.98`); the file uses the padding route.
- Paper-delta candidates:
  - `T2254a` (`B:43-49`, `(eq:termI2)`, `I₃` "exactly the same way" `B:49`): Lean bounds `Σ_y |G_xy||G_yz| <= max_x|G_xx| / η` by the fine-level Ward identity and `max_x |G_xx| ≺ 1` (`STLocalEntry` at `x = y`), and the average `Σ_{x∈[b],z∈[c]} |Ĝ_zx|` by weighted Cauchy-Schwarz through `max 𝓛^(2)_(-,+) ≺ B` (`STLmax`, `k = 2`), not through the entrywise local law `(Gt_bound_flow)` cited at `B:48`; `X_{a'} ≺ B` is `STLK`, `k = 1`.
  - `T2254b` (`B:14` "`σ = +` analogous", used for `LWExpI41K` at `s = true`): the `(+,+)` 2-loop is not positive; Lean uses `|𝓛_(+,+),(a,b)| <= ½(𝓛_(-,+),(a,b) + 𝓛_(-,+),(b,a))` (entrywise AM-GM) and Ward for both orders, the second a column sum `Σ_y |G_yx|² = Im G_xx/η` (refines T2243b).
  - `T2254c` (`B:34` "`J_i` the same way"): with `K = S^(B)(m + m³K⁺)` the column sum `Σ_{a1} |K_{a1 a2}| <= C` (target 1, `C = C_K expC d (c/(d+1))`) replaces `Σ S^(B) = 1`; the constant is absorbed in `N^τ` (refines T2243a).
