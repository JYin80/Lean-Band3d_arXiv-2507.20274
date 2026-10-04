Prover model: claude-sonnet-5-5
## (a) Math preflight — Sun Oct  4 01:56:39 UTC 2026
Notation: `τ=1−t∈(0,1]`, `A=g²+τ`, `B=B_{t,0}=Bparam d L g t 0=A⁻¹+(L^dτ)⁻¹`, `|x|=zdistD` (ℓ¹), `M(δ)=KLmaxDist δ`, `u(δ)=‖Σ^{(∅)}(σ,δ)‖`, root leaf `r`, `b=δ_r`, `s_j=δ_j−b` (so `|s_j|≤M`), `y_j=b−a_j`; `m(+)m(−)=|m|²=1` (`norm_mSigma`), so a long leaf is `Theta(t)` (`thetaEdge`, Partition.lean:166) and `f(a,s)=Θ_t(a,b+s)=θ(y+s)`, `θ(z)=Θ_t(0,z)` (`Theta_apply_add_right_of_three_le` Props4:100). "merged" = on `main`, file:line read in this session.
**(i) Exponent table and proof map**
| # | quantity / step | value, constraint, merged lemma | slack |
|---|---|---|---|
| 1 | `d`, `n` | `3≤d` (`KLShort_holds` KLMolecule:341; `d=k+2` in `expC`); `3≤n`; pin has `σ_r≠σ_{r+1}`. Alternating (`∀j σ_j≠σ_{j+1}` cyclically) forces `n` even, `σ∈{σ_alt,¬σ_alt}`; `n=3` is never alternating (case (i) only); case (ii) has `n≥4` even | `d−2≥1`; `n−2≥1` |
| 2 | **root `r` arbitrary, `σ=¬σ_alt` (finding)** | merged `KLsumZeroAt` (KLMolecule:53, proved :776) is only `σ=KLsigAlt n`, slice `δ_0=x`. No rotation lemma is needed: signed slice sum `=(∏m)Q(σ,∅)` for every `i,x` (`SumZero_sum_slice` KLSumZero:387); `φ(δ)=u(δ)(M+1)^Q` is invariant under `δ↦δ+c` (`SumZero_SigmaPi_add_const` :376) so `Σ_{δ_r=x}φ=Σ_{δ_0=0}φ` (bijection `δ↦δ−δ_0`); `¬σ_alt`: `KLSigmaPi(¬σ,δ)=conj KLSigmaPi(σ,δ)` (`mSigma E (¬s)=conj` Semicircle:85; `Theta(conj ξ)=conj Theta ξ` from `Theta_apply_eq_tsum` Props4:142, real `SBR`; `KLTSPlong n (¬σ) π=KLTSPlong n σ π`) so all norms agree | new small lemmas (4′ below) |
| 3 | `q₁=d−1, q₂=d`, `c=1/2` | `(eq:f12)` for every `s`: `|f₀|≤C_dB` (`KLDecay`, `B_{t,|y|}≤B`); `|f₁|≤C L^τ A⁻¹(|s|+1)^{d−1}/(|y|+1)^{d−1}`, `|f₂|≤C L^τ A⁻¹(|s|+1)^{d}/(|y|+1)^{d}`. Near `|s|≤|y|/2`: `f₁=½[(θ(y+s)−θ(y))−(θ(y−s)−θ(y))]` (`KLDiffOne`, `r=±s`), `f₂=½[θ(y+s)+θ(y−s)−2θ(y)]` (`KLDiffTwo`), `|s|≤(|s|+1)^{d−1}`, `|s|²≤(|s|+1)^d`. Far `|s|>|y|/2`: `θ=θ̊+L^{-d}(1−t)⁻¹` (`Theta0_apply_eq` Props4:243), constant cancels in `f₁,f₂`, `KLZero` gives `≤CL^τA⁻¹`, and `1≤(2(|s|+1)/(|y|+1))^{d}` | needs `q₁≥1,q₂≥2`; slack `d−2`. Constants `2^{d}`·(KL constants at `c=1/2`, `τ'`) |
| 4 | weight `Q` | a term has ≤ `n−1` factors `(|s_j|+1)^{q}`, `q≤d`, so `≤(M+1)^{Q}`, `Q=(n−1)d` (`n=4,d=3`: 9) | — |
| 5 | **needed addition (target 6) `KLsumZero_weighted`** | `∀Q ∃C ∀p, σ∈{σ_alt,¬σ_alt}, n≥4 even, r, x: Σ_{δ_r=x}u(δ)(M+1)^Q ≤ C(g²+τ)`. Not derivable from `KLmolecule_holds` + `KLsumZeroAt` alone (derived here: those allow mass `A` at `M≈c⁻¹log(1/A)`, giving `A·log^Q(1/A)`, unbounded as `g,τ→0` at fixed `L`; the pin is uniform in `g,t`). Proof: nonconstant `δ`: `u≤g²G e^{-cM/2}` (the block `hnc`, KLMolecule:807, from private `KLMolecule_selfW_bound_nc` :546, `KLMolecule_SigmaPi_of_tree` :566, `KLMolecule_edge` :367); constant `δ`: `u≤‖signed‖+Σ_{nc}u` (as :858–867), `‖signed‖≤C_aτ` (`KLSigmaPi_alt_sumZero_le` KLSumZeroWard:1160, `C_a=2^{n²}n·gapK⁻ⁿ·2/√(κ(4−κ))`); `Σ_{δ_0=x}e^{-cM/2}(M+1)^Q≤C_Q` (`sum_exp_decay_centre` PureLoop:144, as :722). Script `w`: ratio bounded in `L` and `τ` | **the nc pointwise bound is private in the merged file**: route A (dispatcher: small ticket making it a public theorem `g²G e^{-cM/2}`, ~40 lines) or route B (KL10a copies the private chain, ~500 lines) |
| 6 | `Σ^{(∅)}` reflection (target 4) | `Σ(σ,c−δ)=Σ(σ,δ)` for all `c`: reflect node labels `b'↦c−b'` in `KLselfW`; `Θ(c−x,c−y)=Θ(x,y)` from `Theta_apply_add_right_of_three_le` + `Theta_transpose_of_three_le` (Props4:95); `1(x,y)` unchanged. With `c=2b`: `g(s)=g(−s)` on `δ_r=b` | translation + symmetry only |
| 7 | case (i) (target 1) | short leaf `j≠r`: `|Θ|≤C_κ(1_{a=δ}+g²e^{-c_κ|·|})≤C_κ(1+g_max²)e^{-c_κ|a_j−δ_j|}` (`KLShort`); other leaves `≤C B` (`KLDecay` if long; `≤C_κ(1+g_max²)≤C B` if short, as `B≥A⁻¹≥(1+g_max²)⁻¹`); `u≤Ce^{-cM}` (`KLmolecule_holds` KLMolecule:610, any `σ`); `e^{-cM}≤∏_{k≠j}e^{-c|δ_k−δ_j|/(n−1)}`; `Σ_δ` closes with `sum_exp_decay_centre` (`expC`, `L`-free) | no `L^τ`, no log |
| 8 | case (ii) split | `Π_{j≠r}(f₀+f₁+f₂)`: `3^{n−1}` patterns `ξ`; groups: (G0) all 0; (G1) one 1, rest 0; (G2) some 2; (G3) no 2, ≥ two 1 (partition of all patterns) | — |
| 9 | (G0) | `Σ_s g(s)Πf₀=(slice sum)·Π_jf₀^j(b)`; `‖slice‖≤C_aτ` (row 2); `n−2` factors `≤C_dB`, one factor summed: `Σ_b|Θ_t(a,b)|≤τ⁻¹` (`sum_norm_Theta_row_le` Props4:210, `(1−t)Σ|Θ|≤1`): `≤C B^{n−2}` | no loss; `τ·τ⁻¹=1` exact |
| 10 | (G1) | `Σ_s g(s)f₁(s_i)=0`: `s↦−s`, `g(−s)=g(s)` (row 6), `f₁(a,−s)=−f₁(a,s)` | exact 0 (script: 2e-18) |
| 11 | (G2) | `≤C L^{nτ'}B^{n−2}·A⁻¹(|y_i|+1)^{-d}·W_Q(b)`, `W_Q≤C_QA` (row 5): `A⁻¹A=1`; `Σ_b(|y_i|+1)^{-d}≤2^d(1+log(dL+1))` (`sum_ball_inv_pow_dim_le` RadialSum:503, `ρ=dL`, `zdistD_le`) `≤C_τ'L^{τ'}` | borderline sum `log L`; slack 0, absorbed by `L^τ` |
| 12 | (G3) | `≤C L^{nτ'}B^{n−3}A⁻²W_Q Σ_b(|y_i|+1)^{-(d−1)}(|y_k|+1)^{-(d−1)}`; `A⁻¹≤B` gives `B^{n−2}`; pair `≤2[(x^d+1)⁻¹(y^{d−2}+1)⁻¹+sym]` (`inv_pow_pair_le` KBound:90, `k=d−2`; `(x+1)^p≥x^p+1`, `(x+1)^d≤2^{d−1}(x^d+1)`), second factor `≤1`, so `Σ_b≤C(1+log L)` (the sharp `O(1)` pair sum is not needed; script `lat`: max 2.0–2.4, saturating) | `2d−2>d`; slack `d−2` |
| 13 | loss `L^τ` | `τ'=τ/n`: ≤ `n−1` factors with `KLDiffOne/Two/Zero` loss plus one `log L≤C_{τ'}L^{τ'}` | exact, `n` factors |
| 14 | lattice sums (target 5) | `p=d−2`: merged `sum_radial_pow_le` RadialSum:192 (`≤C L²`); `p=d`: row 11; `p=d−1` `≤C L`: new, from `sum_radial`+`card_sphere_le` (**not used by the proof**); script `lat`: `S_{d−2}/L²,S_{d−1}/L≤1.6,3.1`, `S_d/(1+log L)≤2.3` | — |
| 15 | `A⁻¹≤B`; `B≥(1+g_max²)⁻¹` | `B−A⁻¹=(L^dτ)⁻¹≥0`; `A≤g_max²+1` since `τ≤1` | — |
| 16 | regimes (§29) | all pins uniform in `τ`: grid `g∈{.05,.5,1}×τ∈{1,10⁻³,10⁻⁶,10⁻⁹}` covers `τ≷g²,g²/L²,g²/L^d` (`g=.05,L=17`: `g²/L²=8.7e-6,g²/L^d=5.1e-7`); `t=0` (`τ=1`) included; `∀n`: pin has `3≤n`, no finite-`n` constraint | — |
| 17 | constants, registry | `C=C(d,n,κ,g_max,τ)` (and `c=1/2`); no `L,g,t,E`. No new hypothesis `Prop`; only `KLPT d κ g_max` (registered, Axioms.lean:79); `KLShort` from `KLShort_holds` | — |
**New targets for KL10a (not in the ticket, needed by KL10b):** (4′) `KLSigmaPi(¬σ,δ)=conj KLSigmaPi(σ,δ)`; `Σ_{δ_r=x}φ=Σ_{δ_0=x'}φ` for translation-invariant `φ` (any `r`); (6) `KLsumZero_weighted` (row 5). `KLindStep_nonAlt` needs neither. The ticket's `|s|≺1` truncation is not available: unweighted ratios grow with `L` (script `f`, UNWEIGHTED).
**(ii) One concrete instance.** `d=3, κ=g_max=1, L=5, g=1/2, E=0, t=9/10` (`τ=0.1`, the probe `KLinst` data), `n=4`, `σ=(+,−,+,−)`, root `r=0`, `a=(0,0,0)^4` (and a spread `a`); hypotheses: `3≤d, 3≤n, 0<κ, 0<g_max, 0<g≤g_max, |E|≤2−κ, 0≤t<1, 3≤L`, `σ_r≠σ_{r+1}`, alternating; `KLPT 3 1 1` external: PT shapes checked in Lean form at this `(L,g)` and as `τ→0` (`KLDecay` with `c_d=1/4`; `KLShort` with `C_κ=140.89,c_κ=0.0846` of merged `prop5Short_holds` as quoted in the T2070 report; `KLDiffOne/Two` at `c=1/2`) (TEAM §8 lesson 14: `(1−t)·rowsum=1`, `L^dτΘ(0,0)→1`). Script `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2100/pre2.py` (md5 145174ee5984c3072d518fc40bd0e325; numpy, FFT, Θ=(1−tμS^B)⁻¹ exact; Σ^{(∅)} from `T_SP(4)={∅,{(0,2)},{(1,3)}}` of equal-charge chords, KLSumZero:865):
```
$ cd scratchpad/T2100; python3 -W ignore pre2.py inst 0; python3 -W ignore pre2.py inst 1
B0=2.9371 A=0.35 m(+)m(-)=1.0; max|Tp(z)-Tp(-z)|=2e-17; signed c0+sum_{y!=0}(Tp+Tn)=0.05263 (T2056 closed form 2/(1+t)-1=1/19=0.05263)
a=[(0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)]: LHS=sum_b|inner|=3.8399, LHS/B0^2=0.4451; groups sum_b|.|/B0^2: (0) 0.0409 (1) 2.0e-18 (2) 0.3649 (3) 0.0425; f0+f1+f2 split error 4e-15
  cross-check lhs() (convolution form, same a): 3.8399; non-alternating sigma=(+,+,+,-), root r=2 (long), same a: LHS/B0^2=0.1005
  1-t=1e-01: L^d(1-t)Theta(0,0)=23.2191 (1-t)rowsum=1.000000 BD1 0.809 BD2 2.427 KLZero 0.622 KLDecay 0.632 KLShort 0.0043
  1-t=1e-06: L^d(1-t)Theta(0,0)=1.0003 (1-t)rowsum=1.000000 BD1 0.845 BD2 2.576 KLZero 0.520 KLDecay 1.350 KLShort 0.0042
  1-t=1e-09: L^d(1-t)Theta(0,0)=1.0000 (1-t)rowsum=1.000000 BD1 0.845 BD2 2.576 KLZero 0.577 KLDecay 1.350 KLShort 0.0042
a=[(0, 0, 0), (1, 0, 0), (0, 1, 2), (2, 2, 2)]: LHS=sum_b|inner|=0.0044, LHS/B0^2=0.0005; groups sum_b|.|/B0^2: (0) 0.0002 (1) 7.8e-20 (2) 0.0007 (3) 0.0002; f0+f1+f2 split error 3e-18
```
Groups: (G1)=0, (G2) dominates, split error ~1e-15; `σ=(+,+,+,−), r=2` (case (i)) ratio 0.1005. Signed `1/19=2/(1+t)−1` matches the merged closed form (T2056).
Ticket (iii) grids (`d=3`; `f`: all `(y,s)`, `L∈{9,17}`, 12 pairs `(g,τ)`; `ind`: exact `Σ_b|Σ_{δ_r=b}Σ^{(∅)}ΠΘ|/B^{n−2}`, `n∈{3,4}`, every `σ`, every long root, 30 configs `a` per root at 7 grid points `(L,g,τ,E)` incl. `L∈{9,17}`, `τ∈{1,10⁻³,10⁻⁶}`, `E=1`; `w`: `n=4` alt, `(|c₀|+Σ_{y≠0}(|Θ^{++}|+|Θ^{−−}|)(|y|+1)^Q)/A`; `lat`):
```
$ for m in f ind w lat; do python3 -W ignore pre2.py $m; done
f   L= 9 max over 12 (g,1-t) in {.05,.5,1}x{1,1e-3,1e-6,1e-9}: |f0|/B0 1.995 | |f1|A(|y|+1)^2/(|s|+1)^2 1.000 | |f2|A(|y|+1)^3/(|s|+1)^3 1.010 | UNWEIGHTED f1 169.0 f2 2197.0 | KLZero 1.997 KLDecay 1.995
f   L=17 max over 12 (g,1-t) in {.05,.5,1}x{1,1e-3,1e-6,1e-9}: |f0|/B0 1.999 | |f1|A(|y|+1)^2/(|s|+1)^2 1.000 | |f2|A(|y|+1)^3/(|s|+1)^3 1.095 | UNWEIGHTED f1 625.0 f2 15625.0 | KLZero 2.000 KLDecay 1.999
ind max over 7 grid points (L,g,1-t,E) x all sigma x all long roots x 30 a: n=3 (never alternating) 3.456 | n=4 non-alternating 1.002 | n=4 alternating 7.124
w   L= 9 max over 5 (g,1-t,E): |signed|/(1-t) 1.000 | sum_{delta_0=x}|Sigma|(M+1)^Q/(g^2+1-t): Q=0 6.000 Q=3 121.42 Q=6 19108.2 Q=9 7291067
w   L=17 max over 5 (g,1-t,E): |signed|/(1-t) 1.000 | sum_{delta_0=x}|Sigma|(M+1)^Q/(g^2+1-t): Q=0 6.000 Q=3 125.33 Q=6 23269.9 Q=9 13584343
w   L=33 max over 5 (g,1-t,E): |signed|/(1-t) 1.000 | sum_{delta_0=x}|Sigma|(M+1)^Q/(g^2+1-t): Q=0 6.000 Q=3 125.34 Q=6 23316.4 Q=9 13809731
lat L= 9 S_{d-2}/L^2 1.324  S_{d-1}/L 2.130  S_d/(1+log L) 1.513  max_c sum_b (|b|+1)^-2 (|c-b|+1)^-2 2.032
lat L=17 S_{d-2}/L^2 1.417  S_{d-1}/L 2.504  S_d/(1+log L) 1.770  max_c sum_b (|b|+1)^-2 (|c-b|+1)^-2 2.207
lat L=33 S_{d-2}/L^2 1.482  S_{d-1}/L 2.818  S_d/(1+log L) 2.018  max_c sum_b (|b|+1)^-2 (|c-b|+1)^-2 2.320
lat L=65 S_{d-2}/L^2 1.522  S_{d-1}/L 3.051  S_d/(1+log L) 2.239  max_c sum_b (|b|+1)^-2 (|c-b|+1)^-2 2.385
```
**Verdicts.** `KLindStep_nonAlt` (1): PASS. `KLf0/1/2` split and identities (2): PASS (algebra). `(eq:f12)` for every `s`, `q₁=d−1,q₂=d` (3): PASS (the unweighted form has a constant growing with `L` at `|s|` up to `L`: script `f`, UNWEIGHTED 169→625 for `f₁`, 2197→15625 for `f₂` from `L=9` to `17`). `KLSigmaPi_reflect` (4): PASS. Lattice sums (5): PASS (only `p=d` is used; `p=d−1` optional). Pin `KLindStepPin`: true as written (no counterexample in any regime; max ratio 7.1 over the grid). Added target 6 `KLsumZero_weighted`: PASS as mathematics; BLOCKED on a public nc pointwise bound only if route B (copy) is refused. Overall for KL10a: **PASS**.
Paper-delta candidates: T2100a (`(eq:f12)` holds for every `s` only with factors `(|s|+1)^{d−1},(|s|+1)^{d}`; the paper states it for `|s|≺1`); T2100b (`(eq:Sigma-empty-sum-zero)` second estimate needed in the weighted form `Σ u(M+1)^Q≤C(g²+τ)`, which follows from the pointwise `g²` factor of nonconstant `δ`).
## (b) Script output (worktree RBM3D-wt/T2100, branch t/T2100; scripts and outputs in scratchpad/T2100/: axscan.lean, clash.sh, extract.py, extract_inst.py, names.lean)
```
$ date -u; git log --format="%h %cd %s" --date=iso-strict main..t/T2100 | cut -c1-110
Sun Oct  4 02:52:36 UTC 2026
b8f3f3f 2026-10-03T19:51:55-07:00 T2100: KL10a rename signed helper with the file stem
3d2addb 2026-10-03T19:49:33-07:00 T2100: KL10a KLlat_pair_rpow
75b5444 2026-10-03T19:44:17-07:00 T2100: KL10a lattice sums in the form C(1 + log L)
1ff370e 2026-10-03T19:39:12-07:00 T2100: KL10a docstrings
be5742a 2026-10-03T19:36:59-07:00 T2100: KL10a instance docs
7742379 2026-10-03T19:35:26-07:00 T2100: KL10a instances (n=4 case (i), nondegenerate weighted sum-zero), docs
49f1ef9 2026-10-03T19:28:51-07:00 T2100: KL10a RBM3D/Loop/KLIndStepA.lean (case (i), leaf split, (eq:f12) all 
$ git status --short; git diff --stat main...t/T2100
 RBM3D/Loop/KLIndStepA.lean | 1479 ++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1479 insertions(+)
$ touch RBM3D/Loop/KLIndStepA.lean; lake build RBM3D.Loop.KLIndStepA 2>&1 | tail -3
Build completed successfully (3255 jobs).
$ wc -l RBM3D/Loop/KLIndStepA.lean; grep -c 'sorry\|admit\|native_decide\|^axiom' RBM3D/Loop/KLIndStepA.lean
    1479 RBM3D/Loop/KLIndStepA.lean
0
$ lake env lean scratchpad/T2100/axscan.lean   # every hand-written constant of the module, private included
module RBM3D.Loop.KLIndStepA: 49 hand-written constants (46 theorems, 3 defs, 11 private); axioms used by them: [propext, Classical.choice, Quot.sound]; constants using another axiom: 0
$ lake env lean scratchpad/T2100/axioms.lean   # #print axioms of the public declarations
38 of 38 lines: [propext, Classical.choice, Quot.sound]; other lines: 0
$ registry pre-check: temporary `import RBM3D.Loop.KLIndStepA` after the last import of RBM3D.lean (reverted, not committed), lake build | grep ...
info: RBM3D.lean:139:0: axiom audit: 3122 theorems, 1148 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
premises found by scanning: 82 (borrowed 2, owed 65, structural 15).
registry: 5 borrowed + 100 owed + 37 structural; 60 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
Build completed successfully (3840 jobs).
$ the same without the import (baseline of this worktree)
info: RBM3D.lean:138:0: axiom audit: 3087 theorems, 1145 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 82 (borrowed 2, owed 65, structural 15).
registry: 5 borrowed + 100 owed + 37 structural; 60 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
Build completed successfully (3839 jobs).
$ bash clash.sh pubnames.txt   # grep -rnw of each public name in main RBM3D/*.lean
clashing names: 0 of 38
$ lake env lean scratchpad/T2100/names.lean | grep -c error   # 47 #check lines of (c)
0
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Loop/KBoundEmpty.lean RBM2D/Loop/KBoundInner.lean   # templates only, nothing ported
 RBM2D/Loop/KBoundEmpty.lean | 210 +++++++------------------------------------
 RBM2D/Loop/KBoundInner.lean | 215 +++++++++-----------------------------------
 2 files changed, 74 insertions(+), 351 deletions(-)
```
Target statements, extracted from the file by `python3 extract.py <names>` (docstrings and proofs omitted):
```lean
noncomputable def KLf0 (f : Zd d L → ℂ) : ℂ := f 0
noncomputable def KLf1 (f : Zd d L → ℂ) (s : Zd d L) : ℂ := (1 / 2 : ℂ) * f s - (1 / 2 : ℂ) * f (-s)
noncomputable def KLf2 (f : Zd d L → ℂ) (s : Zd d L) : ℂ :=
  (1 / 2 : ℂ) * f s + (1 / 2 : ℂ) * f (-s) - f 0
theorem KLf_split (f : Zd d L → ℂ) (s : Zd d L) : KLf0 f + KLf1 f s + KLf2 f s = f s
theorem KLf1_neg (f : Zd d L → ℂ) (s : Zd d L) : KLf1 f (-s) = -KLf1 f s
theorem KLf2_neg (f : Zd d L → ℂ) (s : Zd d L) : KLf2 f (-s) = KLf2 f s
theorem KLf0_bound (hPT : KLPT d κ gmax) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (a b : Zd d p.L),
      ‖KLf0 (fun s => Theta d p.L p.g (p.t : ℂ) a (b + s))‖ ≤ C * Bparam d p.L p.g p.t 0
theorem KLf_crude_bound (hPT : KLPT d κ gmax) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (a b s : Zd d p.L),
      ‖KLf0 (fun s => Theta d p.L p.g (p.t : ℂ) a (b + s))‖ ≤ C * Bparam d p.L p.g p.t 0 ∧
      ‖KLf1 (fun s => Theta d p.L p.g (p.t : ℂ) a (b + s)) s‖ ≤ C * Bparam d p.L p.g p.t 0 ∧
      ‖KLf2 (fun s => Theta d p.L p.g (p.t : ℂ) a (b + s)) s‖ ≤ C * Bparam d p.L p.g p.t 0
theorem KLf12_bound (hd : 3 ≤ d) (hPT : KLPT d κ gmax) (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (a b s : Zd d p.L),
      ‖KLf1 (fun s => Theta d p.L p.g (p.t : ℂ) a (b + s)) s‖
        ≤ C * (p.L : ℝ) ^ τ * (p.g ^ 2 + |1 - p.t|)⁻¹ * (((zdistD d p.L s : ℝ) + 1) ^ (d - 1))
            * ((((zdistD d p.L (a - b) : ℝ) + 1) ^ (d - 1))⁻¹) ∧
      ‖KLf2 (fun s => Theta d p.L p.g (p.t : ℂ) a (b + s)) s‖
        ≤ C * (p.L : ℝ) ^ τ * (p.g ^ 2 + |1 - p.t|)⁻¹ * (((zdistD d p.L s : ℝ) + 1) ^ d)
            * ((((zdistD d p.L (a - b) : ℝ) + 1) ^ d)⁻¹)
theorem KLSigmaPi_reflect (hκ : 0 < κ) (p : KLPar κ gmax) {n : ℕ} [NeZero n] (σ : Fin n → Bool)
    (c : Zd d p.L) (δ : Fin n → Zd d p.L) :
    KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ (fun i => c - δ i)
      = KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ
theorem KLslice_f1_vanish (hκ : 0 < κ) (p : KLPar κ gmax) {n : ℕ} [NeZero n] (σ : Fin n → Bool)
    (r i : Fin n) (b : Zd d p.L) (f : Zd d p.L → ℂ) :
    ∑ δ ∈ univ.filter (fun δ : Fin n → Zd d p.L => δ r = b),
        KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ * KLf1 f (δ i - b) = 0
theorem KLlat_pow_sub_two (k : ℕ) (a : Zd (k + 2) L) :
    ∑ b : Zd (k + 2) L, ((((zdistD (k + 2) L (a - b) : ℕ) : ℝ) + 1) ^ k)⁻¹
      ≤ Real.exp (√((k : ℝ) + 2)) * (2 ^ (k + 2) * radC 1 * (L : ℝ) ^ 2)
theorem KLlat_pow_sub_one (k : ℕ) (a : Zd (k + 2) L) :
    ∑ b : Zd (k + 2) L, ((((zdistD (k + 2) L (a - b) : ℕ) : ℝ) + 1) ^ (k + 1))⁻¹
      ≤ 2 ^ (k + 2) * (((k : ℝ) + 3) * L)
theorem KLlat_pow_dim (k : ℕ) (a : Zd (k + 2) L) :
    ∑ b : Zd (k + 2) L, ((((zdistD (k + 2) L (a - b) : ℕ) : ℝ) + 1) ^ (k + 2))⁻¹
      ≤ 2 ^ (k + 2) * (1 + Real.log (((k : ℝ) + 2) * L + 1))
theorem KLlat_pow_dim_rpow (k : ℕ) {τ : ℝ} (hτ : 0 < τ) (a : Zd (k + 2) L) :
    ∑ b : Zd (k + 2) L, ((((zdistD (k + 2) L (a - b) : ℕ) : ℝ) + 1) ^ (k + 2))⁻¹
      ≤ 2 ^ (k + 2) * (1 + (((k : ℝ) + 2) + 1) ^ τ / τ) * (L : ℝ) ^ τ
theorem KLlat_pow_dim_logL (k : ℕ) (a : Zd (k + 2) L) :
    ∑ b : Zd (k + 2) L, ((((zdistD (k + 2) L (a - b) : ℕ) : ℝ) + 1) ^ (k + 2))⁻¹
      ≤ 2 ^ (k + 2) * ((1 + Real.log (((k : ℝ) + 2) + 1)) * (1 + Real.log L))
theorem KLlat_pair (k : ℕ) (a₁ a₂ : Zd (k + 2) L) :
    ∑ b : Zd (k + 2) L, ((((zdistD (k + 2) L (a₁ - b) : ℕ) : ℝ) + 1) ^ (k + 1)
        * (((zdistD (k + 2) L (a₂ - b) : ℕ) : ℝ) + 1) ^ (k + 1))⁻¹
      ≤ 2 ^ (2 * k + 6) * (1 + Real.log (((k : ℝ) + 2) * L + 1))
theorem KLlat_pair_rpow (k : ℕ) {τ : ℝ} (hτ : 0 < τ) (a₁ a₂ : Zd (k + 2) L) :
    ∑ b : Zd (k + 2) L, ((((zdistD (k + 2) L (a₁ - b) : ℕ) : ℝ) + 1) ^ (k + 1)
        * (((zdistD (k + 2) L (a₂ - b) : ℕ) : ℝ) + 1) ^ (k + 1))⁻¹
      ≤ 2 ^ (2 * k + 6) * (1 + (((k : ℝ) + 2) + 1) ^ τ / τ) * (L : ℝ) ^ τ
theorem KLlat_pair_logL (k : ℕ) (a₁ a₂ : Zd (k + 2) L) :
    ∑ b : Zd (k + 2) L, ((((zdistD (k + 2) L (a₁ - b) : ℕ) : ℝ) + 1) ^ (k + 1)
        * (((zdistD (k + 2) L (a₂ - b) : ℕ) : ℝ) + 1) ^ (k + 1))⁻¹
      ≤ 2 ^ (2 * k + 6) * ((1 + Real.log (((k : ℝ) + 2) + 1)) * (1 + Real.log L))
theorem KLlat_log_le (d : ℕ) (hd : 1 ≤ d) {τ : ℝ} (hτ : 0 < τ) :
    1 + Real.log ((d : ℝ) * L + 1) ≤ (1 + ((d : ℝ) + 1) ^ τ / τ) * (L : ℝ) ^ τ
theorem KLlat_log_le_logL (d : ℕ) :
    1 + Real.log ((d : ℝ) * L + 1) ≤ (1 + Real.log ((d : ℝ) + 1)) * (1 + Real.log L)
theorem KLlat_inv_le_Bparam (t : ℝ) :
    (g ^ 2 + |1 - t|)⁻¹ ≤ Bparam d L g t 0
theorem KLlat_sum_norm_Theta_row_le (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (a : Zd d L) :
    ∑ b, ‖Theta d L g (t : ℂ) a b‖ ≤ (1 - t)⁻¹
theorem KLIndStepA_sumZero_signed (n : ℕ) [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) (hκ : 0 < κ) (hg : 0 < gmax)
    (hshort : KLShort d κ gmax) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin n → Bool), (∀ j, σ j ≠ σ (j + 1)) →
      ∀ (r : Fin n) (x : Zd d p.L),
        ‖∑ δ ∈ univ.filter (fun δ : Fin n → Zd d p.L => δ r = x),
            KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ‖ ≤ C * (1 - p.t)
theorem KLsumZero_weighted (n : ℕ) [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) (hκ : 0 < κ) (hg : 0 < gmax)
    (hshort : KLShort d κ gmax) (Q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin n → Bool), (∀ j, σ j ≠ σ (j + 1)) →
      ∀ (r : Fin n) (x : Zd d p.L),
        ‖∑ δ ∈ univ.filter (fun δ : Fin n → Zd d p.L => δ r = x),
            KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ‖ ≤ C * (1 - p.t) ∧
        ∑ δ ∈ univ.filter (fun δ : Fin n → Zd d p.L => δ r = x),
            ‖KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ‖ * ((KLmaxDist d p.L δ : ℝ) + 1) ^ Q
          ≤ C * (p.g ^ 2 + (1 - p.t))
theorem KLindStep_nonAlt_noloss (n : ℕ) [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) (hκ : 0 < κ)
    (hg : 0 < gmax) (hPT : KLPT d κ gmax) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin n → Bool) (j r : Fin n), j ≠ r →
      σ j = σ (j + 1) → ∀ a : Fin n → Zd d p.L,
      ∑ b : Zd d p.L, ‖∑ δ ∈ univ.filter (fun δ : Fin n → Zd d p.L => δ r = b),
          KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ *
            ∏ i ∈ univ.erase r,
              thetaEdge d p.L p.g (mSigma p.E) p.t (σ i) (σ (i + 1)) (a i) (δ i)‖
        ≤ C * (Bparam d p.L p.g p.t 0) ^ (n - 2)
theorem KLindStep_nonAlt (n : ℕ) [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) (hκ : 0 < κ)
    (hg : 0 < gmax) (hPT : KLPT d κ gmax) :
    ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin n → Bool) (r : Fin n),
      σ r ≠ σ (r + 1) → (¬ ∀ j, σ j ≠ σ (j + 1)) → ∀ a : Fin n → Zd d p.L,
      ∑ b : Zd d p.L, ‖∑ δ ∈ univ.filter (fun δ : Fin n → Zd d p.L => δ r = b),
          KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ *
            ∏ i ∈ univ.erase r,
              thetaEdge d p.L p.g (mSigma p.E) p.t (σ i) (σ (i + 1)) (a i) (δ i)‖
        ≤ C * (p.L : ℝ) ^ τ * (Bparam d p.L p.g p.t 0) ^ (n - 2)
```
Compiled instances: the 15 `example`s of section 7 (d = 3, L = 5, g = 1/2, E = 0, t = 9/10, `KLinstPar`; every deterministic hypothesis discharged, `KLPT 3 1 1` or nothing left); `python3 extract_inst.py` prints the doc line and the line applying the theorem:
```
[1] lines 1263-1271: Target 1, case (i): `n = 3`, `σ = (+,-,+)`, root `r = 0` (long: `σ_0 ≠ σ_1`), the short leaf is
      exact ⟨C, hC, H KLinstPar KLinstσ 0 (by decide) (by decide) KLinsta⟩
[2] lines 1274-1282: Target 1 (no loss), the same data with the short leaf named.
      exact ⟨C, hC, H KLinstPar KLinstσ 2 0 (by decide) (by decide) KLinsta⟩
[3] lines 1285-1292: Target 2: the splitting of a long leaf at a nonzero `s` with `s ≠ -s`.
      refine ⟨?_, KLf_split f s, KLf1_neg f s, KLf2_neg f s⟩
[4] lines 1296-1325: Target 3, `(eq:f12)`: the three bounds at `a = (0,0,0)`, `b = (1,1,1)`, `s = (2,1,0)`
      ≤ C0 * Bparam 3 5 (1 / 2) (9 / 10) 0 := H0 KLinstPar 0 ![1, 1, 1]
[5] lines 1328-1333: Target 4, `KLSigmaPi_reflect`: the reflected label vector `2 - δ` differs from `δ`.
      exact KLSigmaPi_reflect (κ := 1) (gmax := 1) one_pos KLinstPar KLinstσ (1 + 1) KLinsta
[6] lines 1337-1342: Target 4, group (G1): the antisymmetric part integrates to zero on the slice `δ_0 = b`
      KLslice_f1_vanish (κ := 1) (gmax := 1) one_pos KLinstPar KLinstσ 0 1 ![1, 1, 1] _
[7] lines 1345-1356: Target 5: the lattice sums at `d = 3`, `L = 5`, `a = (1,2,3)`, `a' = 0`.
      ⟨KLlat_pow_sub_two 1 ![1, 2, 3], KLlat_pow_sub_one 1 ![1, 2, 3], KLlat_pow_dim 1 ![1, 2, 3],
[8] lines 1359-1363: Target 5, the pair sum in the form `C L^τ` (`d = 3`, `L = 5`, `τ = 1`).
      KLlat_pair_rpow 1 one_pos 0 ![1, 2, 3]
[9] lines 1366-1372: Target 5, the forms `C (1 + log L)` (`d = 3`, `L = 5`).
      ⟨KLlat_pow_dim_logL 1 ![1, 2, 3], KLlat_pair_logL 1 0 ![1, 2, 3]⟩
[10] lines 1375-1381: Target 5, the `L^τ` form, and `(g² + |1-t|)⁻¹ ≤ B_{t,0}`, `(1-t) Σ_b |Θ_t(a,b)| ≤ 1`.
      ⟨KLlat_pow_dim_rpow 1 one_pos ![1, 2, 3], KLlat_inv_le_Bparam (d := 3) (L := 5) (g := 1 / 2) (9 / 10),
[11] lines 1387-1417: Target 6, the weighted sum-zero estimate: `n = 4`, `σ = σ^{(alt)}`, root `r = 1`, `x = 0`,
      have hH := H KLinstPar (KLsigAlt 4) (by decide) 1 0
[12] lines 1420-1427: Target 6, the complement `¬σ^{(alt)}` (also alternating), root `r = 2`: the signed estimate.
      exact ⟨C, hC, (H KLinstPar (fun k => !KLsigAlt 4 k) (by decide) 2 0).1⟩
[13] lines 1431-1440: Case (i) at `n = 4`: `σ = (+,+,+,-)`, root `r = 2` (long: `σ_2 ≠ σ_3`), short leaves `0`, `1`;
      exact ⟨C, hC, H KLinstPar ![true, true, true, false] 2 (by decide) (by decide) ![0, 1, 2, 3]⟩
[14] lines 1444-1461: The crude pointwise bounds (`KLf_crude_bound`) and the signed slice estimate
      exact ⟨C, hC, H KLinstPar 0 ![1, 1, 1] ![2, 1, 0]⟩
[15] lines 1466-1474: The helper lemmas at the instance: `σ^{(alt)}` at `n = 4` is alternating and `n` is even
      ⟨KLIndStepA_alt_cases (KLsigAlt 4) (by decide), KLIndStepA_Qlayer_not 0 (9 / 10) (KLsigAlt 4),
```
Narrative (prover stage 1b; first `date -u` of the stage 01:57:40 UTC, last commit b8f3f3f 02:51:55 UTC):
1. Delivered: `RBM3D/Loop/KLIndStepA.lean` (the only changed file; 38 public + 11 private declarations; build clean, standard axioms, registry pre-check unchanged: 82 premises
   with and without the file). Targets 1-5 and the preflight's added target 6, all with hypotheses only `KLPT d κ gmax` (registered) or `KLShort` (`KLShort_holds`); no new
   `Prop`, so `Test/Axioms.lean` needs no line.
2. Names for KL10b: `KLindStep_nonAlt` (pin shape: `∀ τ, ∃ C, ∀ p σ r, σ_r ≠ σ_{r+1} → ¬alternating → ∀ a`) and `KLindStep_nonAlt_noloss` (no `L^τ`, some `j ≠ r` short);
   `KLf0/1/2` (generic in `f : Zd d L → ℂ`, use `f = fun s => Theta d p.L p.g (p.t:ℂ) a (b + s)`; for alternating `σ` a leaf is `Theta` by `KLIndStepA_thetaEdge_long`);
   `KLf_split`, `KLf1_neg`, `KLf2_neg`; `KLf0_bound`, `KLf_crude_bound`, `KLf12_bound` (`(eq:f12)` for every `s`); `KLSigmaPi_reflect`, `KLslice_f1_vanish`; `KLlat_*`;
   `KLIndStepA_sumZero_signed`, `KLsumZero_weighted`.
3. Groups of case (ii) and what closes them: G0 = signed bound (`KLsumZero_weighted`.1, any root `r`, `x = b`) × `KLf0_bound` × `KLlat_sum_norm_Theta_row_le`; G1 =
   `KLslice_f1_vanish` (exactly 0); G2 = one `KLf12_bound` f₂ factor, the other factors `KLf_crude_bound`, `KLsumZero_weighted`.2 with `Q = d` at `x = b`,
   `KLlat_pow_dim_rpow`; G3 = two f₁ factors, `Q = 2d-2`, `KLlat_pair_rpow`, `KLlat_inv_le_Bparam`. Only the distinguished factors carry `(|s_j|+1)^q`, and `|s_j| = |δ_j -
   δ_r| ≤ max|δ_i - δ_j|` (`KLIndStepA_dist_le_maxDist`), so `Q = 2d` suffices (row 4 of (a) uses `Q = (n-1)d`; the theorem is for every `Q`, no correction).
4. `(eq:f12)` exponents chosen: `q₁ = d-1`, `q₂ = d`, constant `C(d, gmax, τ)`, loss `L^τ`, `c = 1/2`. Near `|s| ≤ |a-b|/2`: `KLDiffOne`, `KLDiffTwo` (`r = ±s`); far:
   `Theta0_apply_eq` removes the constant `L^{-d}(1-t)⁻¹` from `f₁, f₂`, `KLZero` gives `L^τ(g²+|1-t|)⁻¹` and `1 ≤ 2^m ((|s|+1)/(|a-b|+1))^m`.
5. Target 6 reuse: the pointwise `g²` gain for non-constant `δ` is private inside the merged `KLMolecule.lean`. Neither of the preflight's routes was needed: the private
   lemmas `KLMolecule_edge`, `KLMolecule_selfW_bound_nc`, `KLMolecule_SigmaPi_of_tree`, `KLMolecule_same_charge`, `KLMolecule_exists_pair`, `KLMolecule_sum_exp_maxDist` (and
   `KLmSigma_mul_not` of `KLTree.lean`) are reached with Batteries' `open private … from …` (no merged file edited, no text copied); `KLIndStepA_nc_pointwise` is the block
   `hnc` of `KLsumZero_holds` for every `σ`.
6. (4′) of (a): the pointwise conjugation of `KLSigmaPi` is not needed; `¬σ^{(alt)}` is reached through `Qlayer(¬σ,∅) = conj Qlayer(σ,∅)` (`KLIndStepA_Qlayer_not`) and
   `SumZero_sum_slice` (slice sum `= (∏m) Q`, independent of `r`, `x`); the root change of a translation-invariant sum is `KLIndStepA_sum_slice_root`.
7. Case (i) needs no `L^τ` and no `log L`; leaves are bounded by `K₁B_{t,0}` using `B_{t,0} ≥ (g²+|1-t|)⁻¹ ≥ (1+gmax²)⁻¹` for short leaves (`KLIndStepA_leaf`).
8. Instances: 15 examples (listing in (b)); nondegeneracy of the weighted one: the slice sum at root `1` equals `1/19` (merged root-`0` value `KLMolecule_inst_signed_val`,
   moved by `KLIndStepA_sum_slice_root`), so the weighted absolute sum is `≥ 1/19`.
9. DECISIONS §29: time domain `0 ≤ t < 1` is `KLPar`; no `L`-`W` relation is used and `W`, `E`, `g`, `L`, `t` do not enter the constants; all `n ≥ 3` (no `∀ᶠ`).
10. RBM2D templates (c9a24cf, read-only; read after the first commit 49f1ef9, 02:28:51 UTC): `SigmaPi_reflect :999`, `Qlayer_not :1019`, `alt_of_all_ne :1034`,
   `norm_slice_alt_le :1085`, `core_short :542`, `core_alt :817` of `Loop/KBoundEmpty.lean`. The d=3 statements `KLSigmaPi_reflect`, `KLIndStepA_Qlayer_not`,
   `KLIndStepA_alt_cases`, `KLIndStepA_sumZero_signed`, `KLindStep_nonAlt_noloss` correspond to them; no RBM2D text was copied. `core_alt` (symmetrised expansion around
   `T(a_i,u)`, weights `(1+maxDist)^k`, `g = 1`) is not ported: the group expansion is KL10b's.
## (c) Verified Mathlib names used (`#check` of 47 names after `import RBM3D.Loop.KLIndStepA`: 0 errors; 46 of them occur in the file (`Complex.mul_conj` does not); one group per line)
- `Finset.sum_fiberwise`, `Finset.sum_nbij'`, `Finset.mul_prod_erase`, `Finset.add_sum_erase`, `Finset.card_erase_of_mem`, `Finset.sum_le_sum_of_subset_of_nonneg`, `Finset.prod_le_prod₀`
- `Finset.filter_congr`, `Finset.sum_congr`, `Finset.mul_sum`, `Finset.sum_mul`, `Finset.sum_add_distrib`, `Finset.sum_neg_distrib`, `Finset.sum_const`, `Finset.prod_const`, `Finset.card_range`, `Finset.card_univ`, `Fintype.card_fin`
- `norm_sum_le`, `norm_prod`, `Complex.norm_conj`, `Complex.norm_real`, `Real.norm_of_nonneg`, `Complex.conj_ofReal`, `map_inv₀`
- `Real.exp_le_one_iff`, `Real.log_le_rpow_div`, `Real.log_le_log`, `Real.log_mul`, `Real.log_nonneg`, `Real.mul_rpow`, `Real.one_le_rpow`, `Real.rpow_nonneg`
- `pow_add_pow_le`, `inv_anti₀`, `inv_le_one_of_one_le₀`, `one_le_pow₀`, `pow_le_pow_left₀`, `pow_le_pow_right₀`, `le_self_pow₀`
- `Fin.induction`, `Fin.coeSucc_eq_succ`, `Fin.last_add_one`, `Fin.val_succ`, `Fin.val_castSucc`, `Nat.even_iff`; Batteries `open private … from …` (`Batteries.Tactic.OpenPrivate`)
- verified absent or deprecated: `not_even_iff_odd` (`Unknown identifier`), `Fin.coe_castSucc` (deprecated: use `Fin.val_castSucc`); `import Mathlib` has no olean in this worktree (import the project modules)
## (d) Open issues and paper-delta candidates
1. The six `KLMolecule_*` lemmas (and `KLmSigma_mul_not`) are reached by `open private`; a rename in `KLMolecule.lean` or `KLTree.lean` breaks this file. Cleanup (dispatcher): make them public, or move `KLIndStepA_nc_pointwise` into `KLMolecule.lean`.
2. KL10b still owes: the expansion `∏_{i≠r}(f₀+f₁+f₂)` (`Finset.prod_add` twice: `V` = f₂ positions, `U` = f₁ positions), the choice of the distinguished indices, the `3^{n-1}`-term bookkeeping, `L^τ` with `τ' = τ/3`, and the glue `KLindStepPin = nonAlt ∨ alt`. The pair sum is `O(1 + log L)`, not `O(1)` (absorbed by the loss).
3. Constants of `KLf12_bound`, `KLf_crude_bound`, `KLsumZero_*` come from `KLPT`/`KLShort` and are not explicit; they depend on `d, κ, gmax, τ` (and `n, Q`), never on `L, W, g, E, t`.
4. T2100a (stronger/necessary): `(eq:f12)` holds for every `s` only with the factors `(|s|+1)^{d-1}` and `(|s|+1)^d`; the paper states it for `|s| ≺ 1`. The unweighted ratio grows with `L` (preflight script `f`, UNWEIGHTED: `f₁` 169 → 625, `f₂` 2197 → 15625 from `L = 9` to `17`).
5. T2100b (needed form): the second estimate of `(eq:Sigma-empty-sum-zero)` is used weighted, `Σ_{δ_r=x}|Σ^{(∅)}|(max|δ_i-δ_j|+1)^Q ≤ C(g²+|1-t|)` (`KLsumZero_weighted`), derived from the pointwise `g²` factor of a non-constant `δ` and the signed estimate; the paper cites the unweighted one from [RBSO1D] Claim 4.30.
6. T2100c (stronger): case (i) holds without the loss `L^τ` (`KLindStep_nonAlt_noloss`).
7. T2100d (notation): Lean writes the decay profiles `(|x|+1)^p` where the paper writes `|x|^p + 1`; equivalent up to `2^p` (`x^p + 1 ≤ (x+1)^p ≤ 2^p (x^p + 1)`, `pow_add_pow_le`, `KLIndStepA_pow_le`).
8. Interface check (scratch only, not in the file): `proto_G2core` and `proto_G3core` in `scratchpad/T2100/s6.lean` (the `Σ_b Σ_{δ_r=b}` sums of G2/G3 from `KLsumZero_weighted` with `Q = d`, `2d-2`, and `KLlat_pow_dim_rpow`, `KLlat_pair_rpow`) compile against this file; the case (ii) expansion and the glue were not attempted.
