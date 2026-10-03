Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 03:45:26 UTC 2026

Target (one theorem, `RBM.Loop.KLK_isKLoop`): for `d L W`, `NeZero L`, `g E : ℝ`, `3 ≤ L`, `1 ≤ W`, `|E| < 2`: the family `K t I = KLK d L g W E t I` satisfies the three clauses of `IsKLoop d L W g (mSigma E) (Ico 0 1) K`: (1) `∂_t K^{(n)} = (W^d) Σ_{1≤k<l≤n} Σ_{a,b} K(cutL_{k,l}^{(a)}) S^{(B)}_{ab} K(cutR_{k,l}^{(b)})` for `t ∈ [0,1)`, `n ≥ 2` (`pro_dyncalK`, `calGonIND`, paper `1_2_Intro_model_result.tex:990-996`); (2) `K_0 = MLoop` for `n ≥ 2` (`eq:initial_K`, `eq:KMloop`, same file :1000-1011); (3) `K^{(1)} = m(σ)` (:987). No external hypothesis and no new `Prop`; the only inputs are merged lemmas (`norm_SB`, `hasDerivAt_Theta_mul_apply`, `hasDerivAt_kTwo`, `KLsum_cut`, `KLtreeValW_cut`, `KLhasDerivAt_treeValW`).

### (i) Exponent table

| Quantity | Value / formula | Constraint | Slack |
|---|---|---|---|
| `W` power, rhs prefactor | `(W^d)^{+1}` | `(W:ℂ)^d ≠ 0`, from `1 ≤ W` | `W^d ≥ 1`; at `W=2,d=3`: `W^d = 8` |
| `W` power in `K^{(n)}`, `n ≥ 3` | `(W^d)^{-(n-1)}` (`KLn`, `KLtreeValG`) | cut piece lengths `n' = k+n-l+1`, `n'' = l-k+1` | exact identity, see next row |
| `W` bookkeeping per cut | `W^d (W^d)^{-(n'-1)} (W^d)^{-(n''-1)} = (W^d)^{1-(n'+n''-2)}` | `n'+n'' = n+2` (`LoopIdx.length_cutGlueL_add_length_cutGlueR`), so exponent `= -(n-1)` | equality, 0 slack; `n',n'' ≥ 2` so Nat-subtraction `n'-1` is exact; script row 3 below |
| Piece lengths | `n', n'' ∈ [2, n]` | rhs never evaluates `K^{(1)}`; all pieces have length `≤ n` | `n' ≥ 2` since `l ≤ n, k ≥ 1`; `n'' ≥ 2` since `l > k`; also `≤ n` |
| Pair count | `#{(k,l)} = C(n,2) = n + n(n-3)/2` for `n ≥ 3` | `n` leaf pairs `(v+1,v+2)` for `v+1<n` and `(1,n)` for the root `v=n-1`, plus one pair `(i+1,j+1)` per diagonal `(i,j)` of the `n`-gon | exact partition (script row 3); `n=2`: single pair `(1,2)`, no classification, handled by merged `hasDerivAt_kTwo` (`RBM3D/Loop/Primitive.lean:65`) |
| Leaf pair `(v+1,v+2)` / root pair `(1,n)` | `(n', n'') = (n, 2)` / `(2, n)` | the 2-loop piece is `kTwo`, the other is `K^{(n)}` with `a_v := y`; derivative of leaf edge `v`: `μ_v Θ S Θ` | summed over all `F ∈ TSP(n)` (every tree has all `n` leaf edges) |
| Diagonal pair `(i+1,j+1)`, `J=(i,j)`, `w=j-i` | `(n', n'') = (n-w+1, w+1)` = (out piece `KLFOut`, in piece `KLFIn`) | `2 ≤ w ≤ n-2`, so `n'` and `n'' ≥ 3` | `Σ_{F ∋ J} f(KLFOut F J, KLFIn F J) = Σ_{G∈TSP(n'),H∈TSP(n'')} f(G,H)` is `KLsum_cut` (`KLCut.lean:1297`); internal edge `Θ-1` has the same derivative `μ Θ S Θ` |
| Derivative of one edge | `∂_t Θ_{tμ} = μ Θ_{tμ} S^{(B)} Θ_{tμ}`, `μ = m(s)m(s')`, in `Θ-1` too | `‖SB‖ = 1` (`norm_SB`, needs `3 ≤ L`), `‖tμ‖ < 1` | `‖tμ‖ = t` since `|m(σ)| = 1` (`norm_mSigma`, `|E| ≤ 2`); slack `1-t > 0` on `[0,1)`, no slack at `t = 1` (hence `Ico`, `Θ_1` does not exist) |
| `‖SB‖ = 1` | row sums `a0 + 2d g² a0 = 1`, `a0 = (1+2dg²)^{-1}` | `3 ≤ L` (2d distinct neighbours); no condition on `g` | `L=3`: 0 slack; Lean instance `L=5`: slack 2 |
| `|E|<2` | `m(+) = m^{(E)}`, `m(-) = conj` | `|m| = 1` needs `|E| ≤ 2`; `Im m > 0` needs `|E| < 2` | `E=0`: slack 2 |
| Initial value | `Θ_0 = 1` (`Theta_zero`), so leaf edges `= 1` and internal edges `Θ_0 - 1 = 0` | any `F ≠ ∅` has a zero factor, only `F = ∅` survives: `Σ_b Π_v 1(a_v = b) = 1(a_1=…=a_n)` | `K_0^{(n)} = Π m(σ_i) (W^d)^{-(n-1)} 1(a const) = MLoop` exactly; `n=2`: `kTwo` at `t=0` gives the same; script row 4 |
| `K^{(1)}` | `KLK_one` (merged, `KLTree.lean:206`) | all `t`, no hypothesis | exact |
| Frozen-signature match | RBM2D `IsPrimitive L W m T K` / `primRhs` / `primInit` (`Kcal.lean:209-226`) vs merged `IsKLoop d L W g m T K` / `treeEqRhs` / `MLoop` (`Loop/TreeRep.lean:142-162`) | same clauses, same `Set.Ico 0 1`, same `W` normalisation, `W^2 → W^d` only | no incompatibility found; port needs no stop |

Dimension-specific changes of the port: `Z2 L → Zd d L`; `W^2 → W^d` in `treeEqRhs`, `MLoop`, `KLn`; `dTheta` replaced by `hasDerivAt_Theta_mul_apply` (`RBM3D/Propagator/Deriv.lean:108`, entrywise, form `μ * (Θ*SB*Θ) a b`). The tree/cut combinatorics (`TSP`, `KLsum_cut`, widths) is dimension-free.

### (ii) Concrete nondegenerate instance

Numbers: `d=3, L=3, g=1/2, E=0` (`m(±) = ±i`, `μ ∈ {±1}`), `W ∈ {1,2}`, `n ∈ {2,3,4}` (the ticket asks `n ∈ {2,3}`; `n=4` adds trees `{(0,2)}`, `{(1,3)}`, i.e. the internal-edge/diagonal branch), `t ∈ {0.3, 0.7}`, two sign vectors and two random label vectors per `n`. Script (python, no Lean) builds `Θ_ξ = (1-ξS)^{-1}` on `Z_3^3` (27 points, `ℓ¹` periodic distance), `K^{(n)}` from the tree sum with the Lean definitions (`KLtreeValW`, `KLleafPar`, `KLnodePar`, `TSP`, `KLn`, `kTwo`, `cutGlueL/R`), the central difference `h=1e-5`, and the rhs of `pro_dyncalK` using `K` itself on the cut pieces.

```
$ python3 t2020_check.py > out.txt; head -4 out.txt
hyp: |E|<2: True  3<=L: True  d= 3
S symmetric: True  max row sum (=||S|| inf-norm): 1.0000000000000002  row sums all 1: True
|m(+)|,|m(-)| = 1.0 1.0  |t mu| = t for t in {0.3,0.7}
=== W=1
$ python3 t2020_summ.py out.txt
=== W=1 n=2: 8 cases (2 sigma x 2 a x t in 0.3,0.7), max|fd-rhs|=5.07e-10
=== W=1 n=3: 8 cases (2 sigma x 2 a x t in 0.3,0.7), max|fd-rhs|=7.92e-11
=== W=1 n=4: 8 cases (2 sigma x 2 a x t in 0.3,0.7), max|fd-rhs|=1.70e-10
=== W=2 n=2: 8 cases (2 sigma x 2 a x t in 0.3,0.7), max|fd-rhs|=5.64e-11
=== W=2 n=3: 8 cases (2 sigma x 2 a x t in 0.3,0.7), max|fd-rhs|=1.90e-12
=== W=2 n=4: 8 cases (2 sigma x 2 a x t in 0.3,0.7), max|fd-rhs|=6.93e-13
$ grep "init n=4\|K^(1)" out.txt
   init n=4 a=const: K0=1.00000000+0.00000000j MLoop=1.00000000+0.00000000j
   init n=4 a=nonconst: K0=0.00000000+0.00000000j MLoop=0.00000000+0.00000000j
   init n=4 a=const: K0=0.00195312+0.00000000j MLoop=0.00195312+0.00000000j
   init n=4 a=nonconst: K0=0.00000000+0.00000000j MLoop=0.00000000+0.00000000j
K^(1) = m(sigma): True True
$ python3 t2020_count.py | sed -n '2p;3p;4p'
n=4: #pairs=6=C(n,2)=6; leaf=4 diag=2 (n(n-3)/2=2); partition ok=True; W^d-exponent & length range ok=True; diag (n',n'')=(n-w+1,w+1) ok=True
n=5: #pairs=10=C(n,2)=10; leaf=5 diag=5 (n(n-3)/2=5); partition ok=True; W^d-exponent & length range ok=True; diag (n',n'')=(n-w+1,w+1) ok=True
n=6: #pairs=15=C(n,2)=15; leaf=6 diag=9 (n(n-3)/2=9); partition ok=True; W^d-exponent & length range ok=True; diag (n',n'')=(n-w+1,w+1) ok=True
```
(Full outputs: `out.txt` has 48 derivative lines and 12 initial-value lines, `W=1` and `W=2` blocks, all printed `fd` equal `rhs` to the digits shown; the `W=2` initial values `-0.125 = -(1/8)`, `1/512 = 0.00195312` confirm `(W^d)^{-(n-1)}`, `d=3`. Scripts: `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/t2020_{check,summ,count}.py`; `t2020_count.py` covers `n = 3..8`, all rows `ok=True`.)

Hypotheses of the target at this instance: `NeZero 3`, `3 ≤ 3`, `1 ≤ W`, `|0| < 2`, `‖SB‖ = 1` (row sums `1`, shown above), `‖tμ‖ = t < 1` for `t ∈ {0.3, 0.7} ⊂ [0,1)`: all hold simultaneously; `N`, index sets nonempty (27 labels), no collapsed window. Lean instance asked by the ticket: `d=3, L=5, W=2, g=1/2, E=0`; extra check at `L=5` (125 points): `row sums==1: True`, `max row sum: 1.0000000000000002`, `neighbours of 0: 6` (`= 2d`). External hypothesis: none, so no limit computation applies; the `n ≥ 4` bounds are not hypotheses of this target.

Notes for stage 1b: (1) the probe docstring "`t ∈ [0,1)` instead of `[0,1]`" is not in `docs/paper-deltas.md` (`grep -n "\[0, *1)\|\[0,1)"` there returned nothing): candidate `T2020a`; (2) the RBM2D file at `c9a24cf` has 2587 lines; the assembly block starts at `section Assembly` (line 1666), the final theorem is `isPrimitive_Kcal` (`TreeRep.lean:~2555`); `c9a24cf` is an ancestor of the current RBM2D HEAD `9e0f275`.

### Verdict

- `KLK_isKLoop` (= `KLisKLoopPin`): **PASS**. Every exponent closes with equality (`n'+n'' = n+2`), all hypotheses hold at the instance, and the three clauses are verified numerically at `n = 2, 3, 4`, `W = 1, 2`.

## (a′) Preflight corrections — Sat Oct  3 04:20:08 UTC 2026

Four line numbers of (a) do not match the files; none changes a verdict, a statement, the instance, a build or an axiom.
```
$ git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Loop/TreeRep.lean | grep -n "^section Assembly\|^section Pinned\|^theorem isPrimitive_Kcal"
1669:section Assembly
2555:section Pinned
2563:theorem isPrimitive_Kcal :
$ git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Loop/Kcal.lean | grep -n "noncomputable def primRhs\|noncomputable def primInit\|^def IsPrimitive" | cut -c1-40
220:noncomputable def primRhs (W : ℕ)
226:noncomputable def primInit (W : ℕ)
233:def IsPrimitive (W : ℕ) (m : Bool
$ grep -n 'K}^{(1)}_{t,' paper/tex/1_2_Intro_model_result.tex | cut -c1-70
988:$${\cal K}^{(1)}_{t,\sigma,a}=m(\sigma),\quad \forall t\in [0,1],\
```
So in (a): `section Assembly` is at line 1669 (not 1666), `isPrimitive_Kcal` at 2563 (2555 is `section Pinned`), `primRhs`, `primInit`, `IsPrimitive` are at `Kcal.lean:220, 226, 233` (not `209-226`), and `𝒦^{(1)} = m(σ)` is at `1_2_Intro_model_result.tex:988` (not 987).

## (b) Script output

`SP=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/t2020`, `WT=/Users/junyin/Lean_proof/RBM3D-wt/T2020`, `R2=/Users/junyin/Lean_proof/RBM2D`; scripts and raw outputs are in `$SP` (outside the repository; `$SP/../RBM2D_TreeRep_c9a24cf.lean` and `RBM2D_Kcal_c9a24cf.lean` are `git show c9a24cf:...` extracts). Commit under test: `1133530` on `t/T2020`; the working-tree file and `git show HEAD:RBM3D/Loop/KLTreeDeriv.lean` have the same sha256 (`34ef50c8d18216b956a540f849b40a088add897bf407bc8fd1a747a9ebfda2f5`).

### b1 Builds
```
$ cd $WT; rm -f <the 8 build artefacts of KLTreeDeriv under .lake/build: .olean .ilean .trace .c .setup.json and the .hash files>; git log -1 --format='%h %s'; git status --short; lake build RBM3D.Loop.KLTreeDeriv 2>&1 | tail -4
1133530 T2020: KLK_isKLoop, the tree sum solves Def_Ktza (KL3)
✔ [3239/3239] Built RBM3D.Loop.KLTreeDeriv (7.7s)
Build completed successfully (3239 jobs).
$ # full library: RBM3D.lean temporarily gets `import RBM3D.Loop.KLTreeDeriv` after `import RBM3D.Path.Walk` (the hub adds it at merge)
$ lake build > $SP/full_build3.txt 2>&1; echo "lake build exit code: $?" >> $SP/full_build3.txt; cp $SP/RBM3D.lean.orig RBM3D.lean; git status --short; git diff --stat
$ grep -n "axiom audit\|Build completed\|exit code\|warning:" $SP/full_build3.txt | cut -c1-170; grep -c KLTreeDeriv $SP/full_build3.txt
4:warning: RBM3D/Propagator/LaplaceGauss.lean:36:100: This line exceeds the 100 character limit, please shorten it!
8:warning: RBM3D/Path/Walk.lean:599:5: Variable name `hK` is not explicitly referenced.
10:Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
15:info: RBM3D.lean:62:0: axiom audit: 988 theorems, 377 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
51:Build completed successfully (3714 jobs).
52:lake build exit code: 0
0
```
(`git status --short` and `git diff --stat` after the restore printed nothing; the two warnings are in other files and no line of the full build mentions this file.)

### b2 Axioms of every public declaration of the file
```
$ cd $WT && lake env lean $SP/axioms.lean | sed ... | awk ...   # `$SP/axioms.lean` has one `#print axioms RBM.Loop.<name>` per public name; grouped by axiom list
9 declarations depend on exactly [propext, Classical.choice, Quot.sound]: KLK_isKLoop KLTreeDerivInst_isKLoop KLTreeDerivInst_ode_two KLTreeDerivInst_ode_three KLTreeDerivInst_ode_four KLTreeDerivInst_ode_zero KLTreeDerivInst_init_const KLTreeDerivInst_init_nonconst KLTreeDerivInst_one
```

### b3 Target statement (extracted from the file by script) against the pin of `docs/tickets/checks/T2020-check.lean`
```
$ python3 <regex: `theorem KLK_isKLoop :` ... `:= by` in the file; `def KLisKLoopPin : Prop :=` ... in the check file; whitespace-normalised>
pin body : ∀ (d L W : ℕ) [NeZero L] (g E : ℝ), 3 ≤ L → 1 ≤ W → |E| < 2 → IsKLoop d L W g (mSigma E) (Set.Ico 0 1) (fun t I => KLK d L g W E t I)
theorem  : ∀ (d L W : ℕ) [NeZero L] (g E : ℝ), 3 ≤ L → 1 ≤ W → |E| < 2 → IsKLoop d L W g (mSigma E) (Set.Ico 0 1) (fun t I => KLK d L g W E t I)
identical after whitespace normalisation: True
$ lake env lean $SP/pincheck.lean   # `def KLisKLoopPin` copied by script from the check file, then `example : KLisKLoopPin := KLK_isKLoop`, `#print axioms KLK_isKLoop`
'RBM.Loop.KLK_isKLoop' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### b4 The compiled instances (section 4 of the file; `d = 3, L = 5, W = 2, g = 1/2, E = 0`; statements extracted by script)
```
theorem KLTreeDerivInst_isKLoop : IsKLoop 3 5 2 (1 / 2) (mSigma 0) (Set.Ico 0 1) (fun t I => KLK 3 5 (1 / 2) 2 0 t I) := KLK_isKLoop 3 5 2 (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num)
theorem KLTreeDerivInst_ode_two : HasDerivAt (fun s => KLK 3 5 (1 / 2) 2 0 s ⟨[true, false], [0, 1]⟩) (treeEqRhs 3 5 2 (1 / 2) (fun I => KLK 3 5 (1 / 2) 2 0 (9 / 10) I) ⟨[true, false], [0, 1]⟩) (9 / 10)
theorem KLTreeDerivInst_ode_three : HasDerivAt (fun s => KLK 3 5 (1 / 2) 2 0 s (KLloopOf 3 5 KLinstσ KLinsta)) (treeEqRhs 3 5 2 (1 / 2) (fun I => KLK 3 5 (1 / 2) 2 0 (9 / 10) I) (KLloopOf 3 5 KLinstσ KLinsta)) (9 / 10)
theorem KLTreeDerivInst_ode_four : HasDerivAt (fun s => KLK 3 5 (1 / 2) 2 0 s (KLloopOf 3 5 ![true, false, true, false] ![0, 1, 2, 3])) (treeEqRhs 3 5 2 (1 / 2) (fun I => KLK 3 5 (1 / 2) 2 0 (9 / 10) I) (KLloopOf 3 5 ![true, false, true, false] ![0, 1, 2, 3])) (9 / 10)
theorem KLTreeDerivInst_ode_zero : HasDerivAt (fun s => KLK 3 5 (1 / 2) 2 0 s (KLloopOf 3 5 KLinstσ KLinsta)) (treeEqRhs 3 5 2 (1 / 2) (fun I => KLK 3 5 (1 / 2) 2 0 0 I) (KLloopOf 3 5 KLinstσ KLinsta)) 0
theorem KLTreeDerivInst_init_const : KLK 3 5 (1 / 2) 2 0 0 ⟨[true, false, true], [0, 0, 0]⟩ = Complex.I / 64
theorem KLTreeDerivInst_init_nonconst : KLK 3 5 (1 / 2) 2 0 0 (KLloopOf 3 5 KLinstσ KLinsta) = 0
theorem KLTreeDerivInst_one : KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨[true], [0]⟩ = Complex.I
```
Every hypothesis of `KLK_isKLoop` is discharged by `norm_num` (`3 ≤ 5`, `1 ≤ 2`, `|0| < 2`); `t = 9/10` and `t = 0` lie in `Set.Ico 0 1`; the loops have length 2, 3, 4 (alternating charges, distinct labels in `Zd 3 5`, 125 blocks); the other seven are proved from `KLTreeDerivInst_isKLoop` by its projections `.1 .2.1 .2.2`; no hypothesis is another gate's pin.

### b5 Name clash (whole-word `git grep -w` of every declared name of the file in `main:RBM3D/*.lean` and `main:RBM3D.lean`)
```
main = ea34a14
public names (9), whole-word hits on main:RBM3D and main:RBM3D.lean: KLK_isKLoop:0 KLTreeDerivInst_isKLoop:0 KLTreeDerivInst_ode_two:0 KLTreeDerivInst_ode_three:0 KLTreeDerivInst_ode_four:0 KLTreeDerivInst_ode_zero:0 KLTreeDerivInst_init_const:0 KLTreeDerivInst_init_nonconst:0 KLTreeDerivInst_one:0 
private names (41) with a hit: sum_perm4':1 in main:RBM3D/Loop/KLCut.lean  
```
The one private hit is the private `sum_perm4'` of `RBM3D/Loop/KLCut.lean`; private names are module-local, and T2014 (d) said KL3 re-ports it privately.

### b6 Port: source, diff against RBM2D, fidelity
```
$ git -C $R2 --no-optional-locks log -1 --format=%h c9a24cf; git -C $R2 --no-optional-locks log -1 --format=%h; git -C $R2 --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Loop/TreeRep.lean
c9a24cf
9e0f275
 RBM2D/Loop/TreeRep.lean | 58 ++++++++++++++++++-------------------------------
 1 file changed, 21 insertions(+), 37 deletions(-)
$ git -C $R2 --no-optional-locks diff -U0 c9a24cf HEAD -- RBM2D/Loop/TreeRep.lean | sed -n '/^@@ -2020/,$p' | grep '^[-+@]'   # the hunks inside the ported ranges (the others are at old lines 11, 36, 179, 251)
@@ -2020 +2012 @@ private theorem Kgen_one (W : ℕ) (m : Bool
-/-! ### Splitting the pairs `(k, l)` of (2.48) -/
+/-! ### Splitting the pairs `(k, l)` of `(pro_dyncalK)` -/
@@ -2553 +2545 @@ end Final
-/-! ## 3. The pinned theorem -/
+/-! ## 3. The theorem -/
@@ -2555 +2547 @@ end Final
-section Pinned
+section Statements
@@ -2560,2 +2552,2 @@ private theorem TreeRep_norm_mSig {E :
-/-- **`Def_Ktza` for the tree representation** ([50] Lemma 3.4 in `d = 2`): the primitive
-loops `𝒦 = Kcal` solve `(pro_dyncalK)` on `t ∈ [0, 1)` (paper-delta T2004a-1), with the
+/-- **`Def_Ktza` for the tree representation** ([YY_25] Lemma 3.4 in `d = 2`): the primitive
+loops `𝒦 = Kcal` solve `(pro_dyncalK)` on `t ∈ [0, 1)`, with the
@@ -2577,9 +2569 @@ theorem isPrimitive_Kcal :   (9 lines removed: `end Pinned`, the `Checks` block with an `example` and `#print axioms`; 1 line added: `end Statements`)
$ cd $SP && python3 portdiff2.py groups   # per declaration: comments/modifiers dropped, whitespace collapsed, RBM2D text renamed by the map below, compared as strings
6 STATEMENT DIFFERS; 6 statement identical, proof differs; 29 identical after renaming; 1 MISSING in RBM3D
STATEMENT DIFFERS: SB_apply_comm sum_perm4' dTheta sum_edges_swap prod_chains isPrimitive_Kcal->KLK_isKLoop
statement identical, proof differs: hasDerivAt_thetaEdge kTwo_rotate hasDerivAt_Kn diag_pair_term Kgen_zero hasDerivAt_Kgen_two
MISSING in RBM3D: TreeRep_norm_mSig
RBM3D-only (non-instance) declarations: mE_zero_eq
$ lake env lean $SP/defrfl.lean; echo "lean exit: $?"   # Kcal.lean:220-238 (`primRhs`, `primInit`, `IsPrimitive`) renamed by script (`Z2 L ↦ Zd d L`, `SB L ↦ SB d L g`, `W^2 ↦ W^d`), then `treeEqRhs d L W g K I = primRhs3 … := rfl`, `MLoop … = primInit3 … := rfl`, `IsKLoop … ↔ IsPrimitive3 … := Iff.rfl`
lean exit: 0
```
Ported, all `RBM2D/Loop/TreeRep.lean` at `c9a24cf`: `section Assembly` 1669 to `end Final` 2552 (ticket range 1675-2587), `isPrimitive_Kcal` 2563, and the helpers `SB_apply_comm` 64, `hasDerivAt_thetaEdge` 123, `hasDerivAt_thetaEdge'` 132, `kTwo_rotate` 143, `rhs_kTwo_left` 151, `rhs_kTwo_right` 164, `sum_perm4'` 466. RBM1D: nothing. Map: `Z2 L ↦ Zd d L`; `thetaEdge L m ↦ thetaEdge d L g m`; `SB L ↦ SB d L g`; `kTwo L W m ↦ kTwo d L W g m`; `KLtreeValW/KLtreeValG/KLn/KLgen/treeEqRhs/MLoop/IsKLoop L ↦ … d L (g)`; `(W:ℂ)^2 ↦ (W:ℂ)^d`; `dTheta m t ↦ dTheta d L g m t`; the RBM2D bound variable `d` ↦ `ed`; each RBM2D name `x` with a declared `KLx` in `KLTree.lean`/`KLCut.lean` ↦ `KLx`; explicit: `treeValW treeValG Kn Kgen mSig Kcal IsPrimitive primRhs primInit isTSP_of_mem_TSP gval wholeP InArc ArcLe nodes leafPar nodePar IsTSP`.
The 13 non-identical rows: `SB_apply_comm`, `dTheta` get explicit `(d L) [NeZero L] (g)` binders; `sum_perm4'` is the text of `KLCut.lean` (bound index `d`, not renamed); `sum_edges_swap`, `prod_chains`, `diag_pair_term` use a bound function that was `g` and is `φ` (since `g : ℝ` is the coupling); `hasDerivAt_thetaEdge` uses the merged `hasDerivAt_Theta_mul_apply`; `kTwo_rotate`, `hasDerivAt_Kn` get `(g := g)`; `Kgen_zero`, `hasDerivAt_Kgen_two` call the merged `kTwo_zero`, `treeEqRhs_two`, `hasDerivAt_kTwo`; `TreeRep_norm_mSig` is replaced by the merged `norm_mul_mSigma_lt_one`; `isPrimitive_Kcal ↦ KLK_isKLoop` has the pin's statement (b3); `mE_zero_eq` is the instance helper.

### b7 Scope and hygiene
```
$ git diff --stat main...t/T2020; git diff --name-only main...t/T2020   # main = ea34a14
 RBM3D/Loop/KLTreeDeriv.lean | 1153 +++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1153 insertions(+)
RBM3D/Loop/KLTreeDeriv.lean
$ grep -c -E "sorry|admit|native_decide|^axiom|unsafe" RBM3D/Loop/KLTreeDeriv.lean
0
$ lake env lean $SP/privcheck.lean   # constants of the module, from the environment
public (non-internal) constants: 11 = the 9 declared names + KLgen.congr_simp + KLinsta.eq_1 (generated by simp/congr)
private constants (approx., auxiliary lemmas excluded): 41
public statements mentioning a private constant: 0 #[]
```

### Narrative
1. Verdict: the target `RBM.Loop.KLK_isKLoop` is delivered in `RBM3D/Loop/KLTreeDeriv.lean` (1153 lines, commit `1133530` on `t/T2020`). Its type equals the body of `KLisKLoopPin` (b3); `lake build RBM3D.Loop.KLTreeDeriv` and the full `lake build` (temporary root import) succeed and the root audit reports 0 axioms (b1); every public declaration depends only on `propext`, `Classical.choice`, `Quot.sound` (b2); the compiled instance is `KLTreeDerivInst_isKLoop` with seven applications of its clauses (b4); no `sorry`, `admit`, `native_decide` or axiom (b7).
2. Statement: for `3 ≤ L`, `1 ≤ W`, `|E| < 2`, `KLK` satisfies the three clauses of the merged `IsKLoop` on `Set.Ico 0 1`: `(pro_dyncalK)` for `n ≥ 2` (two-sided `HasDerivAt`), `K_0 = MLoop` for `n ≥ 2`, and `K^{(1)} = m(σ)` (merged `KLK_one`). No hypothesis and no new `Prop` were added. This is the existence half of `Def_Ktza`; uniqueness is the pin `KLuniquePin` (KL4).
3. Proof, a port of RBM2D `TreeRep.lean` at `c9a24cf` (b6). The derivative of a tree sum is the merged `KLhasDerivAt_treeValW`: one term per leaf and per internal edge, with `∂_t Θ_{tμ} = μ Θ S^{(B)} Θ` (`hasDerivAt_thetaEdge'`). The leaf `v` gives the pair `(v+1, v+2)`, the root leaf the pair `(1, n)` (`leaf_term`, `leaf_pair_term`, `root_pair_term`: the short piece is `kTwo`, the other is `KLn` with `a_v := x`). A diagonal `(i, j)` gives the pair `(i+1, j+1)` (`treeValW_internal_cut`, `internal_term`, `diag_pair_term`, using `KLtreeValW_cut`, `KLgval_in_eq`, `KLgval_out_eq`, `KLsum_cut`). `sum_pairs` splits `{1 ≤ k < l ≤ n}` into these `n + #diagonals` pairs. `n = 2` is the merged `hasDerivAt_kTwo` through `treeEqRhs_two`. `Kn_zero` is the initial value (`Θ_0 = 1`, only `F = ∅` survives).
4. Dimension: the changes of substance are `Z2 L ↦ Zd d L` and `W^2 ↦ W^d`. The exponent identity `W^d (W^d)⁻¹^{n''-1} (W^d)⁻¹^{n'-1} = (W^d)⁻¹^{n-1}` (`hpow` in `internal_term`) is RBM2D's proof with `((W:ℂ)^d)⁻¹` for `((W:ℂ)^2)⁻¹` and `hW : (W:ℂ)^d ≠ 0`. The cut bijection and the widths are the merged, dimension-free KL2 API. The coupling `g` enters through `SB d L g`, `thetaEdge d L g m`, `kTwo d L W g m` and the merged `norm_SB` (which needs `3 ≤ L`).
5. Merged against RBM2D definitions: by the `rfl` checks of b6, `treeEqRhs`, `MLoop`, `IsKLoop` (`TreeRep.lean:142, 151, 158`) are RBM2D's `primRhs`, `primInit`, `IsPrimitive` (`Kcal.lean:220, 226, 233`) with `Z2 L ↦ Zd d L`, `SB L ↦ SB d L g`, `W^2 ↦ W^d`, and the same `Set.Ico 0 1`. Nothing the port could not absorb, so no stop. RBM2D's `isPrimitive_Kcal` reads `∀ (L W : ℕ) [NeZero L], 3 ≤ L → 1 ≤ W → ∀ E : ℝ, |E| < 2 → IsPrimitive L W (mSig E) (Set.Ico 0 1) (fun t => Kcal L W E t)` (`TreeRep.lean:2563-2565`); `KLK_isKLoop` is the pin (b3): the extra parameters `d` and `g`, `E` before the hypotheses, and `fun t I => …`.
6. Ticket text: it says the merged derivative of `Θ` replaces RBM2D's `dTheta`. RBM2D's `dTheta` (`TreeRep.lean:1850`) is only an abbreviation of the matrix `(μ • (Θ S)) Θ`; it is kept here as a private `abbrev` with explicit `d L g`. The merged `hasDerivAt_Theta_mul_apply` replaces `hasDerivAt_Theta_apply` and the chain rule inside `hasDerivAt_thetaEdge` (`TreeRep.lean:123`).
7. Imports: `Mathlib.Data.List.GetD` (for `List.getD_eq_getElem`, `Mathlib/Data/List/GetD.lean:33`, not reached through the imports of `RBM3D.Loop.KLCut`; RBM2D's `TreeRep.lean` imports it too) and `RBM3D.Loop.KLCut`.
8. Instances (b4): `KLTreeDerivInst_ode_two/three/four` at `t = 9/10` (loops of length 2, 3, 4; the 4-loop has the trees `∅`, `{(0,2)}`, `{(1,3)}`), `KLTreeDerivInst_ode_zero` at the end point `0 ∈ Set.Ico 0 1`, `KLTreeDerivInst_init_const` (`K_0 = (2^3)^{-2} m(+)m(-)m(+) = i/64`), `KLTreeDerivInst_init_nonconst` (`K_0 = 0`), `KLTreeDerivInst_one` (`K^{(1)} = m(+) = i`).
9. State: `RBM3D.lean` was edited only for the full build and is restored (b1: `git status` empty); only the sole writable file is committed (b7). Section (a) is unchanged; (a′) corrects four line numbers.

## (c) Verified Mathlib names used
Each name below resolved in Lean (`$SP/resolve.lean`: a `#resolve` command over the 521 identifier tokens of the file, in `namespace RBM.Loop`, `open Finset`; 151 tokens resolve to non-project names and 83 to project names; output `$SP/resolve.out`). Lemma-like names, by namespace:
`Complex.*`: I
`Fin.*`: ext last last_add_one le_def lt_def prod_univ_eq_prod_range val_add val_add_one_of_lt val_last val_one' val_zero
`Finset.*`: Icc Ico Ioc disjoint_left ext filter image map mem_Icc mem_Ico mem_Ioc mem_image mem_map mem_range mem_sigma mem_union mem_univ mul_sum prod_Ico_add' prod_Ico_consecutive prod_Ico_eq_prod_range prod_boole prod_congr prod_eq_prod_Ico_succ_bot prod_eq_zero prod_range_mul_prod_Ico prod_singleton range sum_add_distrib sum_coe_sort sum_comm sum_congr sum_eq_single sum_eq_zero sum_filter sum_image sum_map sum_mul sum_sigma sum_subset sum_union univ val
`Function.*`: update update_eq_self update_of_ne update_self
`HasDerivAt.*`: const_mul fun_sum
`List.*`: drop drop_zero ext_getElem getD_eq_getElem getElem_map getElem_mem getElem_ofFn length_take nil_append prod_ofFn take take_append_drop take_zero
`Matrix.*`: mul_apply one_apply smul_apply smul_mul transpose_apply
`Nat.*`: Ico_succ_singleton add_sub_cancel add_zero cast_ne_zero lt_or_ge lt_or_gt_of_ne mod_eq_of_lt mod_self sub_add_cancel sub_self
`NeZero.*`: ne
`Prod.*`: ext mk.injEq
`Real.*`: sqrt sqrt_sq
root: absurd add_comm congrFun dite_eq_left dite_eq_right heq_of_eq ite_eq_left ite_eq_right ite_false le_of_lt le_refl le_rfl lt_of_lt_of_le min_eq_left mul_add mul_assoc mul_comm mul_eq_zero_of_right mul_inv_cancel₀ not_and not_lt one_mul pow_add pow_ne_zero pow_succ' smul_eq_mul symm true_imp_iff
Project names used (all merged; resolved by the same script): `norm_SB`, `Theta_transpose_of_three_le`, `hasDerivAt_Theta_mul_apply`, `norm_mul_mSigma_lt_one`, `SB_transpose`, `Theta_zero`, `thetaEdge_comm`, `treeEqRhs_two`, `hasDerivAt_kTwo`, `kTwo_zero`, `KLK_one`, `KLtreeValW_empty`, `KLprod_update_eq`, `KLhasDerivAt_treeValW`, `KLtreeValW_cut`, `KLgval_in_eq`, `KLgval_out_eq`, `KLsum_cut`, `KLunShift_val`, `KLunColP_val`, `KLunCol_col`, `KLunCol_of_le`, `KLunCol_of_gt`, `KLcol_of_le`, `KLcol_of_gt`, `KLshiftIn_val`, `KLshiftOut_val`, `KLinV_val`, `KLoutV_val`, `KLoutEnds_of`, `KLwidth_of_isDiag`, `KLmem_diagonals_iff`, `KLisTSP_of_mem_TSP`, `empty_mem_TSP`, `mem_TSP`, `LoopIdx.length_cutGlueL`, `LoopIdx.length_cutGlueR`.
Names verified absent: `List.getD_eq_getElem` is not visible through the imports of `RBM3D.Loop.KLCut` (`Unknown constant` until `import Mathlib.Data.List.GetD`); no other name was missing.

## (d) Open issues and paper-delta candidates
- `T2020a` (typo, the same as `T2004d`, signed in `docs/DECISIONS.md:142` and absent from `docs/paper-deltas.md`: `grep -c "T2004d\|Def_Ktza"` there prints 0): `Def_Ktza` (`1_2_Intro_model_result.tex:988-989`) states `K^{(1)}` and `K^{(n)}` for `t ∈ [0,1]`; the Lean theorem (the pin) states `(pro_dyncalK)`, the initial value and `K^{(1)} = m(σ)` for `t ∈ Set.Ico 0 1`. Reason: `Θ_{tμ} = (1 - tμ S^{(B)})⁻¹` is used with `‖tμ‖ = t < 1` (`norm_mul_mSigma_lt_one`); (a) records no slack at `t = 1`.
- No other difference between the Lean statement and the paper was found: the `M`-loop simplified to `W^{-(k-1)d} ∏ m 1(a_1 = … = a_k)` is cited as D6 in the docstring of the merged `MLoop`; the cut operators are the merged `cutGlueL/R`.
- Observation: clause 1 of `IsKLoop` is a two-sided derivative also at `t = 0`; it holds because `KLK` is given by the same formula for `|t| < 1` (instance `KLTreeDerivInst_ode_zero`).
- Observation: `sum_perm4'` is now defined twice (private in `KLCut.lean`, private here); every helper of this file is private, so only `KLK_isKLoop` and the `KLTreeDerivInst_*` names are public.
- Downstream, per the ticket: KL4 (uniqueness) and the retirement of `KTreeRep` (KL14) wait for `KLK_isKLoop`.
- For `docs/mathlib-api.md`: `List.getD_eq_getElem` (`Mathlib/Data/List/GetD.lean:33`) needs `import Mathlib.Data.List.GetD`.
