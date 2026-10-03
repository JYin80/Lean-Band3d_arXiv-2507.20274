Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 15:14:30 UTC 2026

Notation: `u>0` flow time, `H_u=√u X` (`seqHflow`), `G=(H_u−z)⁻¹`, `Im z>0`; `X` oriented by `idxKey`: for `key i<key j`, `X_ij=a+ib, X_ji=a−ib` with `a=ω(i,j,true), b=ω(i,j,false)`; `X_ii=ω(i,i,true)`; `gvarF=S_ij/2` off the diagonal, `S_ii` on it (FineModel.lean:89-103, 105-111). Sources: `7_8:294-349`, merged FineModel/Expansions/LDEQuad:302.

### (i) Exponent table (constants and conventions; the ticket has no exponents)
| item | value | constraint | slack / check |
|---|---|---|---|
| `∂_{h_{αw}}`, `key α<key w` | `(1/2√u)(∂_a − i∂_b)` on `(α,w,·)` | `∂h_{αw}=1,∂h_{wα}=0`; `∂_{h_{αw}}H_u=E_{αw}` | `coordinateMatrix(c,true)=E_ij+E_ji, (c,false)=iE_ij−iE_ji` ⇒ `(D_a−iD_b)/2=E_ij`; FD below |
| `key α>key w` | `(1/2√u)(∂_a + i∂_b)` on `(w,α,·)` | same | FD below |
| `α=w` | `(1/√u)∂_a` on `(α,α,true)` (real derivative) | `∂_{h_{αα}}H_u=E_{αα}` | FD below |
| closed forms | `∂G_ij=−G_{iα}G_{wj}`, `∂Ḡ_ij=−conj(G_{iw}G_{αj})` | `∂_{h_{αw}}\bar F=conj(∂_{h_{wα}}F)`; needs **`0<u`** (the `u^{-1/2}`; at `u=0` Lean's `0⁻¹=0` gives `∂=0`) | Stein itself is trivial at `u=0` (`H_0=0=S^{(0)}`) |
| Stein, off-diag `key w<key α` | `E[X_wα F]=E[ω_{c1}F]+iE[ω_{c2}F]=(S_wα/2)E[(∂_a+i∂_b)F]=S_wα E[∂_{x_{αw}}F]` | `gvarF=S/2`, `F,∂_cF` tame | uses `GaussIBP.stein` twice (`c1,c2`); orientation `key α<key w`: `ω(α,w,·)`, `X_wα=a−ib` ⇒ same result; diagonal: `E[ωF]=S_ww E[∂_aF]` |
| flow constant | `E[(H_u)_{wα}F]=√u·S·E[∂_xF]=u·S·E[∂_hF]`, `S^{(u)}=u·svarF` | `∂_x=√u ∂_h` | exact: `√u·√u=u` |
| tameness | `‖G‖≤1/Im z=20`, `|G_ij|≤20` (Hermitian `H_u`); `F` of degree `k`, ℓ¹-coeff `c`: `‖F‖≤c·20^k` | continuous, finitely dependent (slice `n`), poly-bounded | sample `‖G‖=19.9876≤20`; `∂_cF` is again a resolvent polynomial (direction `D_c` has entries `0,±1,±i`: `−√u(GD_cG)_kl=−√u(G_kiG_jl+G_kjG_il)`), degree `k+1`, `‖∂_cF‖≤2k√u c 20^{k+1}` |
| real-direction derivative | `d/dt G_kl(H_u+t√u D_c)=−√u(GD_cG)_kl` | merged `hasDerivAt_inverse_apply` is only along the complex line `s·E_{αw}` (Expansions.lean:63) | **not merged**: stage 1b needs the real-direction/Hermitian-`D` version (from `hasFDerivAt_ringInverse`, as in Expansions.lean:63-77) |
| `E Z_w=0` | `Σ_αH_{wα}G_{αw}=1+zG_ww`, `∂(G_{αw}f)=−G_{αα}G_{ww}f+G_{αw}∂f` | `S=S^{(u)}` in `owxDefect` | exact (script (c)) |
| (Owx) in expectation | `m≠0`, `z+s m=−1/m`, `s=u`, rows of `S^{(u)}` sum `u`, `Sp−m²Sp S^{(u)}=S^{(u)}` | row sum of `svarF`=1: in FineModel.lean:640 only as an `example` (not a named lemma; merged named: `sum_svar_row`, EntryDom.lean:165, for `svar` on `Vtx`, `3≤L`) | instance `u|m|²=0.9411<1` (slack 0.0589, Neumann); all residuals ≤3.5e-16 |
| graph derivative | each solid edge `(σ,circ,s,t)` ↦ `−coeff·[G_{sα}G_{wt}]` (`σ` blue) or `−coeff·[Ḡ_{sw}Ḡ_{αt}]` (red), circ irrelevant (`M` constant); `nS` terms | new vertices `α,w` external: `LGraph (E⊕Fin 2) I` | counters per term `(nS+1,nW,nV,nM)`: `nW,nV` unchanged by definition; `nM` unchanged (`LGraph.nM`, LWVocab:177 counts internal molecules, built from `adj`=waved+`=`-dotted only, which are unchanged) |
| `figAux` | in the probe it is an `NGraph 2 2` (edges `u,v`, no `G`-values) | ∂ of `LGraph.val` is undefined on it | use `figGraph` (LWVocab:253, an `LGraph (Fin 2)(Fin 6)`) instead; reported as note, not FAIL |

### (ii) One concrete instance: `d=3, W=2, L=3, N=216`, `g=1/2` (`SBR` of Block.lean:74), `z=0.3+0.05i`, `u=0.7`, complex Hermitian `X`
Common setup (`t2060_common.py`): `S=svarF` (row sums 1), `X` from the coordinates of FineModel, `x=u=(1,0,0)=36, y=v=(0,1,0)=6`. Scripts in `$S/T2060`, `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad`. Python/numpy, no Lean.

**Item 2** (FD with `eps=1e-6` in the real coordinates, then the Wirtinger combination of the table; one sample): `cd $S/T2060 && python3 t2060_item2.py` (selected rows; all 14 rows have `|diff|≤2.3e-9`)
```
N=216 rowsums(S) min/max 1.000000000000000 1.000000000000000  Im z=0.05 u=0.70 g=0.50
d_h( 36,  6) G   _{ 36,  6}: FD +0.73232506+0.22005112j  closed +0.73232505+0.22005112j  |diff|=1.3e-09
d_h( 36,  6) Gbar_{ 36,  6}: FD +0.00967865+0.03578479j  closed +0.00967865+0.03578479j  |diff|=1.4e-10
d_h(  6, 36) G   _{ 36,  6}: FD +0.00967865-0.03578479j  closed +0.00967865-0.03578479j  |diff|=1.4e-10
d_h(  6, 36) Gbar_{ 36,  6}: FD +0.73232506-0.22005112j  closed +0.73232505-0.22005112j  |diff|=1.3e-09
d_h( 17,  5) G   _{  3, 40}: FD +0.15033797+0.01734833j  closed +0.15033797+0.01734833j  |diff|=1.2e-09
d_h( 36, 36) G   _{ 36,  6}: FD +0.14643978-0.07938305j  closed +0.14643978-0.07938305j  |diff|=1.2e-09
d_h(  6,  6) G   _{  7,  7}: FD -0.03464462+0.02394010j  closed -0.03464462+0.02394010j  |diff|=2.3e-09
item 2 worst |diff| = 2.3e-09
```
**Items 3, 4 (Monte Carlo, 200000 samples, 468 s)**: `cd $S/T2060 && python3 t2060_mc.py 200000`. Item 3: `E[(H_u)_{wα}F]` vs `u S_{wα}E[∂_{h_{αw}}F]`, paired-difference SE; controls = flipped sign, wrong orientation `∂_{h_{wα}}`. Item 4: `E Z_w`, `Z_w=owxDefect(f=F, df α w=∂_{h_{αw}}F)`, control = derivative term dropped. Max `|·|/SE` for the true statements: 2.11 (14 tests); controls separate (up to 468σ, 246σ, 49.8σ, 39.5σ) where the signal is not below the noise (`(w,α)=(36,36)` for `|G_uv|²`, `(36,6)` for `Ḡ_uv`; `w=36,6` for `|G_uv|²`).
```
MC samples=200000 (468s)
--- item 3: E[(H_u)_{w a} F] vs S^(u)_{w a} E[d_{h_{a w}} F];  SE of the paired difference ---
F=abs2 (w,a)=(  6, 36) E[lhs]=+1.186e-05-3.888e-07j E[rhs]=+1.106e-05+2.252e-07j SE(diff)=1.4e-04 |diff|/SE=0.01 | control sign-flip |.|/SE=0.1, wrong-orientation d_{h_{w a}} |.|/SE=0.0
F=abs2 (w,a)=( 36,  6) E[lhs]=+1.186e-05+3.888e-07j E[rhs]=+1.106e-05-2.252e-07j SE(diff)=1.4e-04 |diff|/SE=0.01 | control sign-flip |.|/SE=0.1, wrong-orientation d_{h_{w a}} |.|/SE=0.0
F=abs2 (w,a)=( 36, 36) E[lhs]=+2.839e-03+0.000e+00j E[rhs]=+2.945e-03-3.662e-22j SE(diff)=1.4e-04 |diff|/SE=0.78 | control sign-flip |.|/SE=49.8, wrong-orientation d_{h_{w a}} |.|/SE=0.8
F=gbar (w,a)=(  6, 36) E[lhs]=-2.598e-04-1.783e-05j E[rhs]=+1.979e-05+1.914e-05j SE(diff)=2.3e-04 |diff|/SE=1.21 | control sign-flip |.|/SE=1.2, wrong-orientation d_{h_{w a}} |.|/SE=209.8
F=gbar (w,a)=( 36,  6) E[lhs]=+4.404e-02-1.694e-02j E[rhs]=+4.420e-02-1.677e-02j SE(diff)=2.0e-04 |diff|/SE=1.17 | control sign-flip |.|/SE=467.7, wrong-orientation d_{h_{w a}} |.|/SE=246.6
F=gbar (w,a)=( 36, 36) E[lhs]=-2.098e-04+6.078e-05j E[rhs]=-1.876e-05+9.594e-06j SE(diff)=2.0e-04 |diff|/SE=0.97 | control sign-flip |.|/SE=1.3, wrong-orientation d_{h_{w a}} |.|/SE=1.0
--- item 4: E[Z_w] = 0 (Z_w = owxDefect with f=F, df a w = d_{h_{a w}} F) ---
F=abs2 w=  0 E[Z_w]=+7.742e-05-2.723e-04j SE=3.2e-04 |E Z|/SE=0.87 | control (derivative term dropped) E=-1.952e-03-6.027e-04j |.|/SE=6.4
F=abs2 w= 36 E[Z_w]=-5.350e-04-5.397e-04j SE=3.7e-04 |E Z|/SE=2.05 | control (derivative term dropped) E=-1.289e-02+5.597e-03j |.|/SE=39.5
F=abs2 w=  6 E[Z_w]=+4.791e-05-2.459e-04j SE=3.8e-04 |E Z|/SE=0.66 | control (derivative term dropped) E=-1.234e-02+5.885e-03j |.|/SE=38.7
F=abs2 w=100 E[Z_w]=-2.722e-05-4.018e-04j SE=3.2e-04 |E Z|/SE=1.28 | control (derivative term dropped) E=-7.237e-05-3.865e-04j |.|/SE=1.2
F=gbar w=  0 E[Z_w]=+1.035e-04-2.483e-04j SE=4.7e-04 |E Z|/SE=0.57 | control (derivative term dropped) E=+8.272e-05-1.602e-04j |.|/SE=0.4
F=gbar w= 36 E[Z_w]=+1.699e-05-2.297e-06j SE=4.7e-04 |E Z|/SE=0.04 | control (derivative term dropped) E=+6.368e-05+9.894e-05j |.|/SE=0.2
F=gbar w=  6 E[Z_w]=-5.931e-04+7.894e-04j SE=4.7e-04 |E Z|/SE=2.11 | control (derivative term dropped) E=-6.744e-04+7.513e-04j |.|/SE=2.1
F=gbar w=100 E[Z_w]=+4.857e-05+2.027e-04j SE=4.7e-04 |E Z|/SE=0.45 | control (derivative term dropped) E=+2.655e-05+1.989e-04j |.|/SE=0.4
```
**Item 4, pathwise identity with the model data, tame bounds, and the external hypothesis `GaussIBP`** (exact one-coordinate Gauss–Hermite, 60 nodes, on coordinate `(6,36,true)`, variance `S/2=0.025`; the other coordinates frozen at the sample): `cd $S/T2060 && python3 t2060_ext.py`
```
Tame: ||G||_op = 19.9876 <= 1/Im z = 20.0 ; max|G_ij| = 2.1077 ; max|d_h G_ij| over (al,w,i,j) sampled <= 4.4425 = (1/Im z)^2 = 400.0
GaussIBP.stein, coordinate (6,36,true) var=S/2=0.02500, F=abs2: E[a F] = +5.825169087068e-03+0.000000000000e+00j ; v E[dF/da] = +5.825169087068e-03+0.000000000000e+00j ; |diff| = 1.2e-17
GaussIBP.stein, coordinate (6,36,true), F=gbar: E[a F] = +1.339405817864e-02-2.956945332991e-03j ; v E[dF/da] = +1.339405817864e-02-2.956945332991e-03j ; |diff| = 6.5e-17
polyInt (one coordinate, n=4): E(1+|a|)^4 = 1+4E|a|+6v+4E|a|^3+3v^2 = 1.681733 (finite)
u*|m|^2 = 0.9411 < 1
hyps of owx_defect_identity: m=-0.207780+1.140709j |m|=1.1595  |z+s m+1/m|=1.1e-16  rowsum S^(u)-u max=1.1e-16  |Sp-m^2 Sp S-S| max=3.5e-16  Im z=0.05
(Owx) pathwise, f=|G_uv|^2, x=0: LHS-RHS(expansion) = -1.061757e-02-7.025715e-03j ; -m sum_w(delta+m^2 S+)Z_w = -1.061757e-02-7.025715e-03j ; |diff| = 2.8e-17
```
**Item 5** (`∂_{h_{αw}}` of `LGraph.val` = FD of the value vs the sum of the derivative-graph values with externals extended by `(α,w)`; `owxG1 m` has circ edges `M=mI`; `Sp=S(1−m²S)⁻¹`, `m` the root of `m²+zm+1=0` of `Im m>0`): `cd $S/T2060 && python3 t2060_graph.py` (`nS` terms, counters as in the table)
```
owxG1 (circ edges, M=m I, ext x=0): nS=2 nW=1 nV=1 -> every derivative term nS=3 nW=1 nV=1 (nterms=2 = nS)
  (alpha,w)=( 36,  6): FD d_h val = -9.80673818e-04+1.22858821e-02j   sum of derivative-graph values = -9.80673801e-04+1.22858821e-02j  rel.diff 1.4e-09
  (alpha,w)=(  6, 36): FD d_h val = -3.29561948e-02+3.44509786e-02j   sum of derivative-graph values = -3.29561948e-02+3.44509786e-02j  rel.diff 3.3e-10
  (alpha,w)=(  5, 17): FD d_h val = +6.20950153e-03-2.12158196e-04j   sum of derivative-graph values = +6.20950152e-03-2.12158211e-04j  rel.diff 2.8e-09
  (alpha,w)=( 36, 36): FD d_h val = +2.48504391e-02+3.59989077e-03j   sum of derivative-graph values = +2.48504391e-02+3.59989077e-03j  rel.diff 7.3e-10
two-edge G_{x a} conj(G_{a y}) S_{x a}: nS=2 nW=1 nV=1 -> every derivative term nS=3 nW=1 nV=1 (nterms=2 = nS)
  (alpha,w)=( 36,  6): FD d_h val = +8.23628941e-03-2.25660475e-02j   sum of derivative-graph values = +8.23628939e-03-2.25660475e-02j  rel.diff 5.4e-10
  (alpha,w)=(  6, 36): FD d_h val = +1.70815307e-02+6.54273656e-02j   sum of derivative-graph values = +1.70815306e-02+6.54273656e-02j  rel.diff 3.5e-10
  (alpha,w)=(  5, 17): FD d_h val = +2.05262635e-02+1.20532532e-02j   sum of derivative-graph values = +2.05262636e-02+1.20532532e-02j  rel.diff 9.1e-10
  (alpha,w)=( 36, 36): FD d_h val = -3.15461961e-02-3.52408361e-02j   sum of derivative-graph values = -3.15461961e-02-3.52408361e-02j  rel.diff 4.9e-10
figGraph (LGraph (Fin 2) (Fin 6), ext x=u,y=v): nS=8 nW=4 nV=6 -> every derivative term nS=9 nW=4 nV=6 (nterms=8 = nS)
  (alpha,w)=( 36,  6): FD d_h val = -1.41211374e-03+7.98156453e-04j   sum of derivative-graph values = -1.41211374e-03+7.98156453e-04j  rel.diff 2.9e-10
  (alpha,w)=(  6, 36): FD d_h val = -1.46410680e-03-5.82239980e-04j   sum of derivative-graph values = -1.46410680e-03-5.82239981e-04j  rel.diff 3.1e-10
  (alpha,w)=(  5, 17): FD d_h val = -6.21480212e-04-1.01552335e-03j   sum of derivative-graph values = -6.21480213e-04-1.01552335e-03j  rel.diff 3.7e-10
```
Concrete Lean-instance data (symbolic, no numerics needed): items 3, 4 at `sz0` (`RBM3D/Defs/Sizes.lean:260`: `L 0=4, W 0=32, lam 0=1/64`, `3≤L`), `n=0`, `F=G_xx` (degree 1, `‖F‖≤1/Im z`), `u=1/2`, `z=3/10+i/20`, `GaussIBP sz0` as hypothesis; item 2 at `d=3, L=3, W=2`.

### Verdicts
- Target 1 (copy of probe lines 433-698): PASS (algebra only; independent of the model; `owx_defect_identity` residual 2.8e-17 above).
- Target 2 (derivative, closed forms): PASS with `0<u` as hypothesis of the closed forms; real-direction derivative lemma must be proved (table row), not merged.
- Target 3 (complex Stein): PASS: the variances of `CoordF` give exactly `S_wα=gvarF·2` off the diagonal and `S_ww` on it; the form of 3 holds in both orientations.
- Target 4 (`E Z_w=0`, `(Owx)` in expectation): PASS; the combination needs the row-sum hypothesis `Σ_j svarF=1` (not a named merged lemma) and `Sp` data as hypotheses or proved from the `example` text.
- Target 5 (graph derivative): PASS on `LGraph (E⊕Fin 2) I`; use `figGraph` in place of `figAux`.

## (b) Script output — Sat Oct  3 16:04:41 UTC 2026
Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2060`, branch `t/T2060`, commits `1cf38b5`, `9ec0e8c`. Files: `RBM3D/Graph/LWStein.lean` (1983 lines, new), `RBM3D/Test/Axioms.lean` (+1 registry line). Scratch: `scratchpad/T2060/`.

### b.1 Builds and scope
```
$ lake build RBM3D.Graph.LWStein 2>&1 | grep "LWStein\|Build completed"
Build completed successfully (3320 jobs).
$ lake build 2>&1 | tail -1   # whole library incl. #assert_rbm_axioms; the root import of the module is the hub's
Build completed successfully (3773 jobs).
$ (cd main worktree, HEAD aa42e43) lake env lean -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 <worktree>/RBM3D/Graph/LWStein.lean; echo "exit $?"
exit 0 (output bytes: 0)
$ grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Graph/LWStein.lean
0
$ git diff --stat main...t/T2060
 RBM3D/Graph/LWStein.lean | 1983 ++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean   |    1 +
 2 files changed, 1984 insertions(+)
```
### b.2 Registry pre-check (DECISIONS §20): `import RBM3D` + `import RBM3D.Graph.LWStein` + `#assert_rbm_axioms`
```
$ lake env lean scratchpad/T2060/registry.lean > registry.out; echo "exit $?"      -> exit 0 (no "unregistered premise" error)
premises found by scanning: 48 (borrowed 2, owed 34, structural 12).
registry: 5 borrowed + 43 owed + 26 structural; 26 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
```
### b.3 `#print axioms` of every target (`axioms_targets.lean`, grouped by script) and of the constants of the module (`collectAxioms`; second line includes private and generated ones)
```
18 targets (owx_defect_identity, owx_smallest, owx_second, owx_smallest_E, dhSample_lwG, dhSample_lwG_star, dhSample_lwG_eq_deriv,
  lwPoly_tame1, stein_sample, stein_lwPoly, integral_owxDefect, owx_integral, lwS_isUnit, lwSplus_spec, dhSample_graphVal,
  LGraph.dTerm_counters, LGraph.dTerm_ord, LGraph.dTerms_counters) depend on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean axioms_all.lean; lake env lean axioms_all2.lean
declarations of RBM3D.Graph.LWStein checked: 143 (theorems 104); with a non-standard axiom: 0 #[]
constants of RBM3D.Graph.LWStein (internal and private included) checked: 254 (theorems 198); with a non-standard axiom: 0 #[]
```
### b.4 Item 1 against the probe (script diff; the merged `LWVocab` names force no change)
```
$ diff <(git show eeda441:RBM3D/Probe/T2040Graphs.lean | sed -n 433,697p) <(sed -n 84,348p RBM3D/Graph/LWStein.lean); echo "exit $?"
exit 0
$ diff <(git show eeda441:... | sed -n 730p) <(grep "^end OwxSmallest" RBM3D/Graph/LWStein.lean); echo "exit $?"
exit 0
$ diff <(git show eeda441:... | sed -n 2033,2112p) <(sed -n 1902,1981p RBM3D/Graph/LWStein.lean); echo "exit $?"
exit 0
```
### b.5 Statements, extracted from the file by script (`n|` = line in `LWStein.lean`; proofs cut)
```
521| def dhSample (u : ℝ) (α w : Idx d (sz.L n) (sz.W n)) (F : Sizes.SeqΩ sz → ℂ)
   |     (ω : Sizes.SeqΩ sz) : ℂ :=
   |   if idxKey d (sz.L n) (sz.W n) α < idxKey d (sz.L n) (sz.W n) w then
   |     (2 * (Real.sqrt u : ℂ))⁻¹ *
   |       (lwPartial sz n (α, w, true) F ω - Complex.I * lwPartial sz n (α, w, false) F ω)
   |   else if idxKey d (sz.L n) (sz.W n) w < idxKey d (sz.L n) (sz.W n) α then
   |     (2 * (Real.sqrt u : ℂ))⁻¹ *
   |       (lwPartial sz n (w, α, true) F ω + Complex.I * lwPartial sz n (w, α, false) F ω)
   |   else (Real.sqrt u : ℂ)⁻¹ * lwPartial sz n (α, α, true) F ω
1381| def LGraph.dTerm (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
   |     LGraph (E ⊕ Fin 2) I where
   |   solid := p.2.map (SEdge.map lwEmb) ++ [(lwDEdges p.1).1, (lwDEdges p.1).2]
   |   waved := Γ.waved.map (WEdge.map lwEmb)
   |   dotted := Γ.dotted.map (DEdge.map lwEmb)
   |   coeff := -Γ.coeff
1390| def LGraph.dTerms (Γ : LGraph E I) : List (LGraph (E ⊕ Fin 2) I) :=
   |   (lwSplit Γ.solid).map Γ.dTerm
   | (`Tame1`, line 703: `tame : Tame sz F`, `diff : ∀ c ω, DifferentiableAt ℝ (t ↦ F (update ω ⟨n,c⟩ t)) (ω ⟨n,c⟩)`, `tame_partial : ∀ c, Tame sz (lwPartial sz n c F)`)
561| theorem dhSample_lwG {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) (α w i j : Idx d (sz.L n) (sz.W n))
   |     (ω : Sizes.SeqΩ sz) :
   |     dhSample sz n u α w (lwG sz n z u i j) ω = -(lwG sz n z u i α ω * lwG sz n z u w j ω) :=
591| theorem dhSample_lwG_star {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u)
   |     (α w i j : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
   |     dhSample sz n u α w (fun ω => star (lwG sz n z u i j ω)) ω =
   |       -star (lwG sz n z u i w ω * lwG sz n z u α j ω) :=
965| theorem lwPoly_tame1 {z : ℂ} (hz : 0 < z.im) (u : ℝ)
   |     (P : MvPolynomial (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) × Bool) ℂ) :
   |     Tame1 sz n (lwPoly sz n z u P) :=
1013| theorem stein_sample (hG : GaussIBP sz) {F : Sizes.SeqΩ sz → ℂ} (hF : Tame1 sz n F) {u : ℝ}
   |     (hu : 0 ≤ u) (α w : Idx d (sz.L n) (sz.W n)) :
   |     ∫ ω, sz.seqHflow n u ω w α * F ω ∂(Sizes.seqP sz) =
   |       lwS sz n u w α * ∫ ω, dhSample sz n u α w F ω ∂(Sizes.seqP sz) :=
1108| theorem stein_lwPoly (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 ≤ u)
   |     (P : MvPolynomial (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) × Bool) ℂ)
   |     (α w : Idx d (sz.L n) (sz.W n)) :
   |     ∫ ω, sz.seqHflow n u ω w α * lwPoly sz n z u P ω ∂(Sizes.seqP sz) =
   |       lwS sz n u w α * ∫ ω, dhSample sz n u α w (lwPoly sz n z u P) ω ∂(Sizes.seqP sz) :=
1136| theorem integral_owxDefect (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u)
   |     (P : MvPolynomial (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) × Bool) ℂ)
   |     (w : Idx d (sz.L n) (sz.W n)) :
   |     ∫ ω, owxDefect z (lwGm sz n z u ω) (lwS sz n u) (lwPoly sz n z u P ω)
   |       (fun α w' => dhSample sz n u α w' (lwPoly sz n z u P) ω) w ∂(Sizes.seqP sz) = 0 :=
1239| theorem owx_integral (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) {m : ℂ}
   |     (hm0 : m ≠ 0) (hzm : z + (u : ℂ) * m = -m⁻¹)
   |     (Sp : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
   |     (hSp : ∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j)
   |     (P : MvPolynomial (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) × Bool) ℂ)
   |     (x : Idx d (sz.L n) (sz.W n)) :
   |     ∫ ω, (lwG sz n z u x x ω - m) * lwPoly sz n z u P ω ∂(Sizes.seqP sz) =
   |       ∫ ω, (m * ∑ α, lwS sz n u x α * (lwG sz n z u x x ω - m) * (lwG sz n z u α α ω - m) *
   |             lwPoly sz n z u P ω +
   |           m ^ 3 * ∑ α, ∑ β, Sp x α * lwS sz n u α β * (lwG sz n z u α α ω - m) *
   |             (lwG sz n z u β β ω - m) * lwPoly sz n z u P ω -
   |           m * ∑ α, lwS sz n u x α * lwG sz n z u α x ω * dhSample sz n u α x (lwPoly sz n z u P) ω -
   |           m ^ 3 * ∑ α, ∑ β, Sp x α * lwS sz n u α β * lwG sz n z u β α ω *
   |             dhSample sz n u β α (lwPoly sz n z u P) ω) ∂(Sizes.seqP sz) :=
1562| theorem dhSample_graphVal [Fintype I] [DecidableEq I] (hz : 0 < z.im) (hu : 0 < u) (Γ : LGraph E I)
   |     (ℓe : E → Idx d (sz.L n) (sz.W n)) (α w : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
   |     dhSample sz n u α w (fun ω => Γ.val (lwSampleData sz n z u M S Sp ω) ℓe) ω =
   |       (Γ.dTerms.map fun Γ' => Γ'.val (lwSampleData sz n z u M S Sp ω) (Sum.elim ℓe ![α, w])).sum :=
1619| theorem LGraph.dTerm_counters (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
   |     (hp : p ∈ lwSplit Γ.solid) :
   |     (Γ.dTerm p).nS = Γ.nS + 1 ∧ (Γ.dTerm p).nW = Γ.nW ∧ (Γ.dTerm p).nV = Γ.nV ∧
   |       (Γ.dTerm p).nM = Γ.nM :=
1656| theorem LGraph.dTerm_ord (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
   |     (hp : p ∈ lwSplit Γ.solid) : ord (Γ.dTerm p).counters = ord Γ.counters + 1 :=
```
### b.6 Compiled nonempty instances (`example`s and `LWInstOwx` theorems; first line of each docstring)
```
L1696: Item 2 at `d = 3`, `L = 3`, `W = 2` (`N = 216`), `z = 0.3 + 0.05 i`, `u = 7/10`, at every sample `ω` (in particu
L1708: Item 2 at a fixed sample and fixed vertices (`0` and `(1, 0, 0)` in `Z_6^3`).
L1746: Tameness of a resolvent polynomial at `d = 3`, `L = 3`, `W = 2`: `|G_{00}|² + 2` (`G_{00} \bar G_{00} + 2`), `u 
L1750: (no docstring) example (ω : Sizes.SeqΩ lwSzT) (i j : Idx 3 (lwSzT.L 0) (lwSzT.W 0)) :
L1758: The convention of `dhSample` against the matrix-level complex derivative along `E_{αw}`, at `d = 3`, `L = 3`, `W
L1768: Item 3 at `sz0` (`d = 3`, `L = 4`, `W = 32`, `n = 0`), `F = G_{xx}`, `u = 1/2`: the complex Stein identity `E[(H
L1778: Item 3 at a concrete off-diagonal pair: `w = 0`, `α = (32, 0, 0)` (the pair of the `FineModel` check of `E|X_{wα
L1788: Item 3 for a resolvent polynomial with a red factor at `sz0`: `F = |G_{xy}|² = G_{xy} \bar G_{xy}` with `x = 0`,
L1793: Item 4 at `sz0`, `f = G_{xx}`, `df α w = -G_{xα} G_{wx}`: `E Z_w = 0` for the Stein defect of the row `w`.
L1803: Item 4, `(Owx)` in expectation, at `sz0`: `f = G_{xx}`, `u = 1/2`, `m = i/2`, `z = 7i/4`, `S⁺ = S (1 - m² S)⁻¹`;
L1843: Item 5 on `owxG1` (`m Σ_α S_{xα} Ǧ_{xx} Ǧ_{αα}`, `d = 3`, `L = 4`, `W = 32`): the derivative of the value is the
L1860: Item 5 on a two-edge graph `S_{xa} G_{xa} \bar G_{ay}` (here with `d = 3`, `L = 3`, `W = 2`).
L1877: Item 5 on the merged `figGraph` (the left graph of `fig:p=2expansion`, `n_S = 8`, `n_W = 4`, `n_V = 6`, `n_M = 2
L1933: `(Owx)` for `Ǧ_{xx}`, instantiated (two vertices, `m = i`, `z = 0`, `s = 1`).
L1940: `(Owx)` for `Ǧ_{xx} G_{xy}`, instantiated (four terms, `x = 0`, `y = 1`).
L1950: `(Owx)` in expectation, instantiated on an arbitrary probability space with a random `G` (any measurable family)
L1971: `(Owx)` in expectation at a fully concrete point (`Ω = Unit` with the point mass, `G = M`): every hypothesis, th
```
### b.7 Name clashes; b.8 ports
```
checked 143 names against `import RBM3D` of the main worktree; clashes: 1 [RBM.Gauss.coordinateMatrix.congr_simp]
```
The one hit has the last component `congr_simp`: Lean's generated congruence lemma of the merged `RBM.Gauss.coordinateMatrix`, not a declaration written here. My first name `lwD` for the sample data clashed with `LWVocab`'s `lwD` and was renamed `lwSampleData` before this check. No port from RBM1D or RBM2D (nothing copied from them, no diff-stat); item 1 and `LWInstOwx` are copied from the T2040 probe `eeda441`, text-identical (b.4).

### Narrative
1. Scope. All five targets are in `RBM3D/Graph/LWStein.lean` (namespace `RBM.Graph`): item 1 text-identical to the probe; item 2 `dhSample`,
   `dhSample_lwG`, `dhSample_lwG_star`, and `dhSample_lwG_eq_deriv` (for `G_{ij}` it equals the complex-line derivative of the merged
   `hasDerivAt_inverse_apply`); item 3 `Tame1`, `lwPoly`, `lwPoly_tame1`, `stein_sample`, `stein_lwPoly`; item 4 `integral_owxDefect`,
   `owx_integral`; item 5 `LGraph.dTerm(s)`, `dhSample_graphVal`, `LGraph.dTerm_counters`, `LGraph.dTerm_ord`.
2. Convention T2060a (docstring of `dhSample`): `h_{αw} = √u X_{αw}`, `X` oriented by `idxKey` as in `Xentry`; `∂_{h_{αw}} = (2√u)⁻¹ (∂_a ∓ i ∂_b)` on the two
   coordinates of the entry, `u^{-1/2} ∂_a` on the diagonal, so `∂h_{αw} = 1`, `∂h_{wα} = 0`. At `u = 0` it is `0` (Lean's `0⁻¹ = 0`): the closed forms
   and the graph derivative take `0 < u`; the Stein identity takes `0 ≤ u`.
3. The real-direction derivative of the inverse (`lwStein_hasDerivAt_inv`, from `hasFDerivAt_ringInverse`) is proved here, as (a) required; the merged
   lemma is the complex line. The closed forms are the combinations `(∂_a ∓ i ∂_b)/2` of `-√u (G D_c G)`, with `D_c = coordinateMatrix c`
   (`E_{ab} + E_{ba}`, `i E_{ab} - i E_{ba}`, `E_{aa}`; `lwStein_coordMat_*`).
4. Stein (`stein_sample`): case split on the `idxKey` order of `(w, α)`, two applications of `GaussIBP.stein` (variances `S/2` off the diagonal, `S` on it:
   `lwStein_gvar_off/diag`), then `√u √u = u`. `GaussIBP sz` is the only hypothesis. `Tame1` is closed under `+ - ×`, `star`, finite sums and list products;
   `lwPoly_tame1` is `MvPolynomial.induction_on`; the leaf bound is the merged envelope `‖G_{ij}‖ ≤ |Im z|⁻¹` (`norm_inverse_entry_le`, via `Gauss/FlowCalculus`).
5. `E Z_w = 0`: `stein_sample` for `G_{αw} f`, the Leibniz rule `lwStein_dh_mul`, the closed form and the resolvent identity `lwStein_resolvent_id`, summed over `α`.
   `owx_integral` is the pathwise `owx_defect_identity` (item 1) integrated; as in the probe's `owx_smallest_E` it takes `Sp` with `Sp - m² Sp S = S` and `z + u m = -m⁻¹`
   as hypotheses. `lwS_row_sum` (rows of `S^{(u)}` sum to `u`, `3 ≤ L`) is proved here (copy of the FineModel `example`); `lwSplus`, `lwS_isUnit`, `lwSplus_spec` show the
   hypothesis is satisfiable when `|m|² u < 1`.
6. Graph derivative: terms indexed by `lwSplit Γ.solid` (position-wise Leibniz list, `lwStein_dh_listProd`), no `Fin` indexing. The new vertices `α = inl (inr 0)`,
   `w = inl (inr 1)` are external: `Γ.dTerm p : LGraph (E ⊕ Fin 2) I`; blue `a→b` ↦ `a→α`, `w→b`; red ↦ `a→w`, `α→b`; coefficient `-coeff`; circle dropped (`M` constant).
   `n_M` is unchanged: `nM` reads only waved and `=`-dotted edges (`lwStein_nM_congr`); `disjUnion`, `counters_relabel_equiv`, `lwStein_nM_empty` compare with `Γ`.
7. Imports beyond the ticket's list (never `RBM3D`): `RBM3D.Gauss.FlowCalculus` (merged: `Gres`, continuity of the resolvent, and through it the envelope),
   `Mathlib.Algebra.MvPolynomial.Basic`, `Mathlib.LinearAlgebra.Matrix.Gershgorin`.
8. Instance data (b.6): items 2, 5 at `lwSzT` (`d = 3, L = 3, W = 2`, `z = 0.3 + 0.05 i`, `u = 7/10`, as in (a)); items 3, 4, 5 at `sz0` with `GaussIBP sz0` the only
   hypothesis. For item 4 I took `u = 1/2`, `m = i/2`, `z = 7i/4` instead of (a)'s `z = 3/10 + i/20`: then `z + u m = -m⁻¹` is exact and `|m|² u = 1/8 < 1` gives `Sp`;
   the numeric Part A data of (a) was not re-run in Lean. `LWInstOwx` (probe lines 2033-2112, instance code outside the ticket's reading range) instantiates item 1.
9. Registry: one structural line, `RBM.Graph.Tame1` (a new `Prop` taken as hypothesis by `stein_sample`). The pre-check exited 0 before the line was added as well (the scan counts a
   `Prop` as proved when a theorem concludes it, and `lwPoly_tame1` does); after it the build and the pre-check are as in b.1, b.2. (a) was not edited and needed no (a′).

## (c) Verified Mathlib names (`lake env lean scratchpad/T2060/mathlib_names.lean`: present 48 of 48, none deprecated)
`hasFDerivAt_ringInverse`, `Matrix.entryLinearMap`, `LinearMap.toContinuousLinearMap`, `HasFDerivAt.comp_hasDerivAt`, `deriv.star`, `DifferentiableAt.star`, `deriv_add`,
`deriv_sub`, `deriv_mul`, `MvPolynomial.induction_on`, `MvPolynomial.eval_X`, `det_ne_zero_of_sum_row_lt_diag`, `Matrix.isUnit_iff_isUnit_det`, `Ring.mul_inverse_cancel`,
`Ring.inverse_mul_cancel`, `Ring.inverse_unit`, `Finset.add_sum_erase`, `norm_sub_norm_le`, `MeasureTheory.integral_finsetSum`, `MeasureTheory.integrable_finsetSum`,
`MeasureTheory.integral_sub`, `MeasureTheory.integral_add`, `MeasureTheory.integral_const_mul`, `List.sum_map_mul_left`, `List.map_congr_left`, `List.mem_map`,
`Matrix.smul_single`, `Matrix.mul_smul`, `Matrix.smul_mul`, `Real.sqrt_pos`, `Real.mul_self_sqrt`, `Complex.ofReal_mul`, `inv_mul_eq_iff_eq_mul₀`, `Complex.I_sq`,
`Equiv.sumEmpty`, `Equiv.sumCongr`, `SimpleGraph.Reachable.refl`, `Finset.image_eq_empty`, `Finset.filter_eq_empty_iff`, `Function.update_eq_self`, `Complex.star_def`,
`ite_eq_left`, `ite_eq_right`, `Finset.sum_erase_eq_sub`, `Matrix.single_apply`, `Pi.single_apply`, `Complex.norm_real`, `abs_of_nonneg`
Absent: `Matrix.det_ne_zero_of_sum_row_lt_diag` (the lemma is root-level, `Mathlib/LinearAlgebra/Matrix/Gershgorin.lean:63`); `RBM.continuous_green_of_isHermitian` (merged as `RBM.Gauss.continuous_green_of_isHermitian`).
Deprecated, avoided: `MeasureTheory.integrable_finset_sum` (use `integrable_finsetSum`).

## (d) Open issues and paper-delta candidates (cited as asked: T2040d = `lwPoly`, T2040i = T2060a)
- T2060a (numbers D65 = T2040i): `∂_{h_{αw}}` (undefined in §7) is the Wirtinger derivative in the real coordinates of `X_{αw}` (b.5; `dhSample`); for `G` it is the complex-line derivative along `E_{αw}`.
- T2060b: the paper's `=_𝔼` in `(Owx)` is read as equality of the integrals of the two sides (`owx_integral`), for every resolvent polynomial `f` and the flow data `S = u·svarF`, `z + u m = -m⁻¹` (T2040e).
- T2060c: the Stein identity uses the model's variances (real diagonal `S_{ww}`, off-diagonal `S/2` per real coordinate), for `u ≥ 0`, with `GaussIBP` (owed, S1-19) as hypothesis.
- T2060d: the derivative terms of `(Owx)` are graphs with `α, w` as new vertices; here they are two new external vertices (`E ⊕ Fin 2`); summing over `α` and `w = x` are the step of LW-05..07.
- T2060e: the paper defines `S⁺` through `Θ^{(+,+)}` (`7_8:110`; `S/(1-m²S)` is a comment there); Lean takes any `Sp` with `Sp (1 - m² S) = S` and shows by `lwS_isUnit` that `S (1 - m² S)⁻¹` is one when `|m|² u < 1`.
- Open: (1) `GaussIBP` is not proved here; every probabilistic statement and instance carries it. (2) `(Oe1x)`, `(Oe2x)` are not touched (the expansion tickets). (3) The probe's pin `lwdf` uses a matrix-level
  `dH`; `dhSample` is matched to a matrix-level derivative only for blue entries (`dhSample_lwG_eq_deriv`), the red rule is proved at sample level. (4) `figAux` is an `NGraph` (no `G` values, (a)); the `figGraph` instance replaces it.
