Prover model: claude-sonnet-5-5
## (a) Math preflight — Sat Oct 10 04:19:49 UTC 2026

Scripts are in the scratchpad `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/966b45d4-be15-4db2-88b3-45a074bfecd5/scratchpad/T2370` (not in the repository): `c3.py` (the C3 mirror), `instance.py`, `summ.py`; `kode.py`, `mgraph.py`, `mirror.py` are T2367's (`cmp` against `../T2367/*.py`: `same kode`, `same mgraph`, `same mirror`). No Lean was written. Notation: `Q = M^{(σσ')}` (`BAMss`), `Θ = (1 - tQ)⁻¹`, `K` a family with `BASplicedFam`, `I = KLloopOf σ a`.

### (i) Exponent table
| quantity | value | constraint | slack |
|---|---|---|---|
| `n` | `≥ 3` (targets 2, 3, 4 and `BASplicedFam` clause 3) | the leaf pairs `(v+1,v+2)`, `v ≤ n-2`, and `(1,n)` are pairwise distinct iff `n ≥ 3` (at `n = 2` both are `(1,2)`) | 0 at `n = 3` (3 leaf pairs = all 3 pairs of `treeEqRhsS`); `n(n-3)/2` diagonal pairs stay for K05b |
| piece lengths (`TreeRep.lean:75-82`, `length_cutGlueL = k + n - l + 1`, `length_cutGlueR = l - k + 1`) | leaf `v ≤ n-2`, `(k,l) = (v+1,v+2)`: `L` has length `n`, `R` has length `2`. Wrap `(1,n)`: `L` has length `2`, `R` has length `n` | length `2` is the closed form (clause 2), length `n ≥ 3` is clause 3; `p + q = n + 2` | exact; the 2-piece is never `BAGamma` at `n = 2` (C1) |
| `W` power | LHS `(W^d)^{-(n-1)}`; RHS `W^d · (W^d)^{-(n-1)} · (W^d)^{-1}` | equal when `W^d ≠ 0` | exact. If `W^d = 0` (`W = 0`, `d ≥ 1`): RHS term has the factor `W^d = 0`; LHS has `0^{n-1}`, `n - 1 ≥ 2`; both `0`. No hypothesis `W ≠ 0` is needed (the pin has none) |
| `t` | `0 ≤ t < 1` | `BATheta_hasDerivAt`, `BATheta_resolvent` (hypotheses `0 ≤ t < 1`, `BAReal`) | instance `t = 1/2`; the `t`-range is the pin's |
| leaf derivative | `∂_tΘ = ΘQΘ`, entrywise (`BATheta_hasDerivAt`), `(ΘQΘ)(a_v,·) = Σ_b (ΘQ)(a_v,b) Θ(b,·)` | rewrites to `Σ_b (ΘQ)(a_v,b) Γ_F(a_v ← b)` | FD of `Θ` vs `ΘQΘ`: `4.4e-13` (9 configs) |
| chord derivative | `∂_t(tΘ) = Θ + tΘQΘ = Θ·Θ` by the right resolvent identity `Θ = 1 + tΘQ` (`BATheta_resolvent`, 2nd conjunct) | the pin's chord weight is `Θ · Θ` | FD of `tΘ` vs `Θ·Θ`: `3.0e-13`; resolvent residual `4.4e-16` |
| `M`-edge derivative | `0` (constant in `t`) | `BACactusValEdgeW`: `Sum.inr s ↦ M(BAMcharge F σ s)` | exact |
| orientation / wrap (C2) | needs `Θ^{(s',s)} = Θ^{(s,s')}`, `Q^{(s',s)} = Q^{(s,s')}`, `Qᵀ = Q`, `Θᵀ = Θ`, `ΘQ = QΘ` | all at the BA data (`BATheta_swap`, `BATheta_isSymm`, `BAMB_symm`, resolvent); `M(σ)` symmetric | `swap 4.4e-16`, `symm 3.3e-16`, `commute 4.4e-16` (9 configs). No non-symmetric `M` anywhere: no C2 failure |
| `d`, `L` | `d` free (no `3 ≤ d`), `NeZero L` | targets quantify `∀ L [NeZero L]`, `BAReal d L g κ E m` | instance `(d,L) = (3,4)` |
| (a) tolerance (FD) | 9-point stencil, `h = 2e-3` | `≤ 1e-8` (ticket) | measured abs `9.07e-9` (n = 6), rel `5.4e-11`; slack factor `1.1` absolute (finite-difference truncation/roundoff, not the identity), `187` relative |
| (b) tolerance | exact algebra | `≤ 1e-12` (ticket), stop line `1e-10` | leaf `4.1e-14`, wrap `7.1e-14`: factor `14` below `1e-12`, `1400` below the stop line |
| size | central `≈ 1250` lines (table in (iv)) | stop line `2000` (binding) at each section boundary | `750` below the stop line; the ticket's estimate is `800 / 1100 / 1600` |

### (ii) Concrete nondegenerate instance and the C3 per-term numerics
**Hypotheses of the targets:** target 2: `BAReal d L g κ E m`, `3 ≤ n`, `KLIsTSP F`, `0 ≤ t < 1`; target 3: `BAReal`, `BASplicedFam d L W g E m K`, `3 ≤ n`, `0 ≤ t < 1`, any `W`; target 4: none (`BAKcac_spliced` proves `BASplicedFam`; clause 2 is the closed form, clause 3 the cactus sum). No external hypothesis, so no limit computation is owed; `BAReal = BASelf ∧ κ ≤ Im m` is checked at the data (`BASelf`: `0 < Im m ∧ m = L^{-d} tr M^{(B)}`).
**Instance** `(d,L) = (3,4)` (the family of `BA/MFixedPoint.lean:893`), `N = L^d = 64`, `W = 2` (`W^d = 8`), `g = 1/2`, `E = 0.3`, `t = 1/2`, `κ = Im m`, `n = 3`, `F = ∅`, all 8 `σ`, random `a`. `Psi` is built as a Kronecker sum and compared entrywise with `Adj` (`zdistD (x - y) = 1`, the `ℓ¹` torus distance of `Defs/Lattice.lean:71,108`). `cd $S; python3 instance.py`:
```
Psi == Adj (l1 torus nearest neighbours, RBM.Adj): True  N = L^d = 64  symmetric: True
m = -0.096078036194+0.681402583263j; BASelf residual |m - L^-d tr M| = 2.3e-16; Im m = 0.681403 > 0: True; kappa := Im m: kappa <= Im m: True
M(+) symmetric (BAMB_symm): True  t = 1/2 in [0,1): True  n = 3 >= 3, F = empty in TSP 3 (KLIsTSP): True, 3 <= d, 3 <= L: True
Theta^{(+,-)} row sums = (1-t)^-1: 2.664535460986613e-15
n = 3, all 8 sigma, 4 random a each (96 leaf pairs): (a) max|FD - BAGammaDerivRHS| = 2.56e-12 (max |dGamma| = 5.03e-01);  (b) leaf v<=1: 1.40e-20  wrap v=2: 1.36e-19
K^(3)_{(+,+,-),(0,5,17)}(t=1/2) = (4.268565237911053e-06-1.3597154998869048e-05j) ; 2-loop piece K(cutGlueR(1,2,x=5,I0)) = (-0.000524534322329753-0.00024272823408731493j)  nonzero: True
```
(The hypotheses `3 ≤ d`, `3 ≤ L`, `KLIsTSP ∅` are printed as constants; the others are computed.)

**C3 per-term numerics (binding).** `c3.py` mirrors, as Lean text: `BACactusVal` (T2367's `mirror.cactus_val`, slots/`next`/charge/`KLgval`, open index `a`), `KLloopOf` (pair of lists), `cutGlueL/R` (1-indexed `take`/`drop`, `TreeRep.lean:75-82`), `treeEqRhsS` at `S = 1` (`W^d Σ_{k<l} Σ_x K(cutL x) K(cutR x)`, `KLTree.lean`), the closed-form 2-loop `W^{-d}(Θ Q)(a₁,a₂)`, and `BAGammaDerivRHS` (leaf part `Σ_b (ΘQ)(a_v,b) Γ_F(a_v ← b)`, chord part = `KLgval` with the chord-`J` weight replaced by `Θ·Θ`). No ODE. Data: `d = 1`, `q ∈ {4,5}`, `E = 0.3`, `g ∈ {0.2,0.5}`, `t ∈ {0.3,0.7}`, `W = 1`, plus `(q,g,t) = (4,0.5,0.7)` at `W = 2` (tests the `W` powers): 9 configurations. `n = 3..6`, every `F ∈ TSP n`, every `σ`; (a) is checked for all `a` (open index), (b) for all `a` at `n ≤ 4` and 6 random `a` at `n = 5, 6`. (a): each `Γ_F` derivative by the 9-point finite difference against `BAGammaDerivRHS`. (b): for each leaf `v`, `W^{-d(n-1)} Σ_F` (leaf-`v` term) against the `treeEqRhsS` summand of `(v+1,v+2)` (`v ≤ n-2`) or `(1,n)` (`v = n-1`). (c), informational for K05b: total `W^{-d(n-1)} Σ_F ∂_tΓ_F` (leaf + chord parts) against the whole `treeEqRhsS`. List identities: `cutGlueL (v+1)(v+2) x I = KLloopOf σ (update a v x)`, `cutGlueR (v+1)(v+2) x I = ⟨[σ_v,σ_{v+1}],[a_v,x]⟩`, `cutGlueL 1 n x I = ⟨[σ_0,σ_{n-1}],[x,a_{n-1}]⟩`, `cutGlueR 1 n x I = KLloopOf σ (update a (n-1) x)`, asserted for all `n, σ`, sampled `a, x`. Command `cd $S; python3 c3.py 6 > c3_out.txt; python3 summ.py` (`summ.py` takes the max over the 9 configurations; `c3.py` ran 425 s):
```
n  #TSP  (a)abs      (a)rel     (b)leaf    (b)wrap    (c)total   list-identity checks
3     1  2.10e-12  3.08e-13  1.78e-15  1.86e-15  7.11e-15   39360
4     3  3.90e-11  1.15e-12  2.84e-14  2.14e-14  9.95e-14   483840
5    11  1.21e-10  2.66e-12  7.11e-15  4.44e-15  8.88e-15   17280
6    45  9.07e-09  5.36e-11  4.10e-14  7.11e-14  1.85e-13   41472
matrix-level max over 9 configs: dTheta=4.4e-13 resolvent=4.4e-16 commute=4.4e-16 symm=3.3e-16 swap=4.4e-16 dTT=3.0e-13
MAX over all: (a) abs 9.07e-09 rel 5.36e-11  (b) leaf 4.10e-14   (b) wrap 7.11e-14   (c) total 1.85e-13
```
**(a) max `9.07e-9` ≤ `1e-8` (finite-difference error; relative `5.4e-11`); (b) max `7.1e-14` ≤ `1e-12` and ≤ `1e-10`: the stop line is not triggered.** The (c) column shows that leaf pairs plus diagonal pairs already match the full derivative at `n ≤ 6` (K05b's input).

### (iii) The written argument (targets 2 and 3), K00 convention `σ_i` on `(a_{i-1},a_i)`; leaf `v` carries `Θ^{(σ_v,σ_{v+1})}`, indices `v+1` in `Fin n`
**Target 2.** `Γ_F(s) = KLgval = Σ_b (∏_v Θ_s^{(σ_v,σ_{v+1})}(a_v, b(leaf v))) ∏_e E_e(s)(b(src e), b(tgt e))`, edges `e ∈ ↥F ⊕ BAslot F`: chord `J`: `(s:ℂ)•Θ_s^{(σ_i,σ_j)}`, `M`-edge: `M(BAMcharge F σ s)` constant. A finite sum of finite products of `ℝ → ℂ` functions each `HasDerivAt` at `t ∈ [0,1)`:
- leaf `v`: `(ΘQΘ)(a_v, b(leaf v))` (`BATheta_hasDerivAt`, bridge `BAThetaOf (BAMsigma ..) = BATheta` by `rfl`);
- chord `J`: `(Θ + tΘQΘ)(x,y) = (ΘΘ)(x,y)` (`BATheta_resolvent` 2nd conjunct, `ofReal` has derivative 1);
- `M`-edge: `0`.
Product rule (generic lemma over `KLgval`): the derivative is `Σ_ℓ KLgval(leaf-ℓ weight ← its derivative) + Σ_e KLgval(edge-e weight ← its derivative)` (`Finset.prod_update_of_mem`); `Σ_e` over `Sum.inl J` gives the chord terms of `BAGammaDerivRHS` (`Function.update … (Sum.inl J) (Θ*Θ)`); `Sum.inr s` terms contain the zero matrix, so vanish. Leaf `v`: the leaf-`v` weight row `(ΘQΘ)(a_v,·) = Σ_b (ΘQ)(a_v,b)Θ(b,·)` and `Θ(b,·)` is the leaf-`v` weight at label `b`, so the term is `Σ_b (ΘQ)(a_v,b) Γ_F(σ, update a v b)`. Hypotheses used: `BAReal`, `0 ≤ t < 1`; `KLIsTSP F` and `3 ≤ n` are not used (the pin carries them; unused-variable only).
**Target 3.** Write `Λ_v := Σ_b (Θ^{(σ_v,σ_{v+1})}Q^{(σ_v,σ_{v+1})})(a_v,b) K t (KLloopOf σ (update a v b))`.
- LHS = `Σ_v Λ_v`: `Finset.sum_comm` over `F, v, b` and clause 3 of `K` at `(σ, update a v b)`, `(W^d)⁻¹^{n-1}` kept outside.
- RHS term `v`, `v ≤ n-2`, `(k,l) = (v+1,v+2)`, `l ≤ n`: `cutGlueL = ⟨take (v+1) σ ++ drop (v+1) σ, take v a ++ x :: drop (v+1) a⟩ = KLloopOf σ (update a v x)` and `cutGlueR = ⟨[σ_v,σ_{v+1}],[a_v,x]⟩`; clause 2 gives `K(cutGlueR) = (W^d)⁻¹ (Θ^{(σ_v,σ_{v+1})}Q^{(σ_v,σ_{v+1})})(a_v,x)`; `W^d (W^d)⁻¹ = 1` (case `W^d = 0` above) gives `Λ_v`.
- Wrap `v = n-1`, `(k,l) = (1,n)`, `σ(v+1) = σ_0`: `cutGlueL = ⟨[σ_0,σ_{n-1}],[x,a_{n-1}]⟩`, `cutGlueR = ⟨σ, take (n-1) a ++ [x]⟩ = KLloopOf σ (update a (n-1) x)`. Clause 2 gives `(W^d)⁻¹ (Θ^{(σ_0,σ_{n-1})}Q^{(σ_0,σ_{n-1})})(x, a_{n-1})`, but `Λ_{n-1}` has `(Θ^{(σ_{n-1},σ_0)}Q^{(σ_{n-1},σ_0)})(a_{n-1}, x)`. With `P := ΘQ`: swap of the superscripts (`BATheta_swap`; `Q^{(s',s)} = Q^{(s,s')}` from `BAMB_symm`), `Pᵀ = QᵀΘᵀ = QΘ = ΘQ = P` (`Qᵀ = Q` from `M(σ)` symmetric, `BATheta_isSymm`, `ΘQ = QΘ` from the two resolvent identities, `t ≠ 0`; `Θ_0 = 1` at `t = 0`). So `P'(a_{n-1},x) = P(x,a_{n-1})`.
- List facts (public, stem `KLloopOf_`): the four identities above, the `getD` form of `List.ofFn`. The bookkeeping is `take/drop` of `List.ofFn` against `Function.update` (`List.ext_getElem`, `List.set_eq_take_append_cons_drop`-style); the values at `n = 4` are also `decide`/`rfl` instances.
**Target 4.** `BAKcac d L W g E m t I` is defined by cases: `0` if `¬ I.WF`; length 1: `PropSpin m (I.σ.getD 0 false)`; length 2: `(W^d)⁻¹ (Θ Q)(I.a.getD 0 0, I.a.getD 1 0)` with `Θ, Q` at `(I.σ.getD 0 false, I.σ.getD 1 false)`; length `N ≥ 3`: `(W^d)⁻¹^{N-1} Σ_{F ∈ TSP N} BAGamma …` on `Fin N` with `getD` (`NeZero N` from the length). `BAKcac_spliced`: clauses 1, 2 by `simp` on `[s]`, `[σ₁,σ₂]`; clause 3 at `KLloopOf σ a`, whose length is `n` propositionally: generalize `N = n` and `subst`, with `(List.ofFn σ).getD i false = σ i`. This is the shape of `KLgen` (`KLTree.lean:135-150`).

### (iv) Plan, lines against the stop line `2000` (`wc -l BA/KTreeDeriv.lean` at each section commit)
| § | content | lines |
|---|---|---|
| 0 | header, imports, the four pins verbatim | 75 |
| 1 | matrix facts: `M(σ)` symmetric (private; `BAKBase_Msigma_symm` is private), `Q` symmetric, `Q` swap, `ΘQ = QΘ`, `(ΘQ)ᵀ = ΘQ`, swapped `P` | 110 |
| 2 | generic product rule for `KLgval` (leaf and edge parts), leaf-row rewrite, zero-matrix edge terms, `Sum` split | 270 |
| 3 | `baGamma_hasDerivAt` (entry derivatives, assembly) | 120 |
| **commit 1** | **≈ 575** | |
| 4 | `KLloopOf_*` list identities (4 + `getD`) | 170 |
| 5 | `BAKcac`, `BAKcac_spliced` | 150 |
| **commit 2** | **≈ 895** | |
| 6 | `baLeafPairs`: Fubini, per-`v` pair lemma (two cases), sum assembly | 270 |
| 7 | instances: `baGamma_hasDerivAt`, `baLeafPairs` at the flow point `P` of `(3,4)`, `n = 3`, `F = ∅`, `BAKcac`; list identities at `n = 4` by `decide`; registry pre-check | 100 |
| **total** | central `≈ 1265` (low `800`, high `1600`) | `735` below `2000` |
Risks: §4 (`take/drop` with `update`) and §5 (`Fin I.length` cast); if a section boundary exceeds `2000`, commit, stop, RETURN.

### Verdicts
Target 1 (pins): PASS (definitions; no hypothesis beyond the pinned statements). Target 2 `baGamma_hasDerivAt`: PASS. Target 3 `baLeafPairs`: PASS (no extra hypothesis; `W^d = 0` handled by case; wrap pair via C2 at the BA data). Target 4 `BAKcac`, `BAKcac_spliced`: PASS. Stop line (b) not triggered. **Overall: PASS.** Candidate `T2370a`: `baLeafPairs` takes `W : ℕ` with no `0 < W`; the equality holds also at `W^d = 0` (both sides `0`); no other paper-delta candidate arises in the leaf part; the tree-representation gap (design §3 (a)) is unchanged.

## (b) Script output — Sat Oct 10 06:07:33 UTC 2026
Worktree `WT=/Users/junyin/Lean_proof/RBM3D-wt/T2370`, branch `t/T2370`, cwd `WT`; `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/966b45d4-be15-4db2-88b3-45a074bfecd5/scratchpad/T2370` holds the scripts (`mkpins.py`, `extract_*.py`, `summ.py`) and scratch Lean files, none in the repository.
**1. Build (`lake env lean` prints nothing = no warning, no error) and the section commits (stop rule: `wc -l` ≤ 2000 at each section commit)**
```
$ lake build RBM3D.BA.KTreeDeriv 2>&1 | tail -1; lake env lean RBM3D/BA/KTreeDeriv.lean; echo "lake env lean exit=$?"; for c in $(git log --reverse --format=%h main..t/T2370); do echo "$c $(git show $c:RBM3D/BA/KTreeDeriv.lean | wc -l | tr -d " ") lines  $(git log -1 --format=%s $c | cut -c1-72)"; done
Build completed successfully (3741 jobs).
lake env lean exit=0
a623d7e 285 lines  T2370: BA/KTreeDeriv sections 0-3 (pins, matrix facts, product rule on K
2864401 417 lines  T2370: BA/KTreeDeriv sections 4-5 (KLloopOf cutGlue list facts, BAKcac, 
e187401 513 lines  T2370: BA/KTreeDeriv section 6 (baLeafPairs)
6af976f 603 lines  T2370: BA/KTreeDeriv section 7 (compiled instances at the flow point P; 
7422664 612 lines  T2370: BA/KTreeDeriv final (drop unused hypothesis of KLloopOf_cutGlueL_
d8bc699 612 lines  T2370: BA/KTreeDeriv docstring accuracy (resolvent conjunct, instance da
```
**2. `#print axioms` of every public declaration of the file (list by `grep -nE "^(theorem|def|noncomputable def) "` into `public_decls.txt`)**
```
$ lake env lean $S/lean/ax_final.lean 2>&1 | sed "s/ depends on axioms:/ :/"
'RBM.BA.BASplicedFam' : [propext, Classical.choice, Quot.sound]
'RBM.BA.BAGammaDerivRHS' : [propext, Classical.choice, Quot.sound]
'RBM.BA.BAGammaDerivStmt' : [propext, Classical.choice, Quot.sound]
'RBM.BA.BALeafPairsStmt' : [propext, Classical.choice, Quot.sound]
'RBM.BA.baGamma_hasDerivAt' : [propext, Classical.choice, Quot.sound]
'RBM.BA.KLloopOf_cutGlueL_leaf' : [propext, Quot.sound]
'RBM.BA.KLloopOf_cutGlueR_leaf' : [propext, Classical.choice, Quot.sound]
'RBM.BA.KLloopOf_cutGlueL_wrap' : [propext, Classical.choice, Quot.sound]
'RBM.BA.KLloopOf_cutGlueR_wrap' : [propext, Classical.choice, Quot.sound]
'RBM.BA.BAKcac' : [propext, Classical.choice, Quot.sound]
'RBM.BA.BAKcac_spliced' : [propext, Classical.choice, Quot.sound]
'RBM.BA.baLeafPairs' : [propext, Classical.choice, Quot.sound]
```
**3. Pins against the check file (`mkpins.py`: Part 1 body vs section 0; then `pins.lean`: the four `rfl` equalities with the check copies, the targets and `BAKcac_spliced` against the check statements)**
```
$ python3 $S/mkpins.py && lake env lean $S/lean/pins.lean; echo "exit=$?"
pins block (check file Part 1 body) == file section 0 (whitespace-normalised): True
exit=0
```
**4. Target statements, extracted from the file by script (`baGamma_hasDerivAt`, `baLeafPairs` are one-liners whose statements are the pins; `variable` lines of the sections `Lists` and `Kcac`)**
```
$ python3 $S/extract_stmts.py baGamma_hasDerivAt baLeafPairs BAKcac BAKcac_spliced KLloopOf_cutGlueL_leaf KLloopOf_cutGlueR_leaf KLloopOf_cutGlueL_wrap KLloopOf_cutGlueR_wrap; grep -n "^variable" RBM3D/BA/KTreeDeriv.lean | awk -F: '$1>=280 && $1<=400'; python3 $S/extract_block.py BAGammaDerivStmt BALeafPairsStmt
-- line 249
theorem baGamma_hasDerivAt (d : ℕ) : BAGammaDerivStmt d := by
-- line 463
theorem baLeafPairs (d : ℕ) : BALeafPairsStmt d := by
-- line 379
noncomputable def BAKcac (t : ℝ) (I : LoopIdx (Zd d L)) : ℂ :=
-- line 411
theorem BAKcac_spliced : BASplicedFam d L W g E m (BAKcac d L W g E m) := by
-- line 308
theorem KLloopOf_cutGlueL_leaf {n : ℕ} (σ : Fin n → Bool) (a : Fin n → Zd d L) (v : Fin n) (x : Zd d L) :
    (KLloopOf d L σ a).cutGlueL (v.val + 1) (v.val + 2) x = KLloopOf d L σ (Function.update a v x) := by
-- line 314
theorem KLloopOf_cutGlueR_leaf {n : ℕ} [NeZero n] (σ : Fin n → Bool) (a : Fin n → Zd d L) (v : Fin n)
    (hv : v.val + 1 < n) (x : Zd d L) :
    (KLloopOf d L σ a).cutGlueR (v.val + 1) (v.val + 2) x = ⟨[σ v, σ (v + 1)], [a v, x]⟩ := by
-- line 333
theorem KLloopOf_cutGlueL_wrap {n : ℕ} [NeZero n] (σ : Fin n → Bool) (a : Fin n → Zd d L) (v : Fin n)
    (hv : v.val + 1 = n) (x : Zd d L) :
    (KLloopOf d L σ a).cutGlueL 1 n x = ⟨[σ 0, σ v], [x, a v]⟩ := by
-- line 355
theorem KLloopOf_cutGlueR_wrap {n : ℕ} (σ : Fin n → Bool) (a : Fin n → Zd d L) (v : Fin n)
    (hv : v.val + 1 = n) (x : Zd d L) :
    (KLloopOf d L σ a).cutGlueR 1 n x = KLloopOf d L σ (Function.update a v x) := by
289:variable {d L : ℕ}
374:variable (d L W : ℕ) [NeZero L] (g E : ℝ) (m : ℂ)
393:variable {d L W g E m}
def BAGammaDerivStmt (d : ℕ) : Prop :=
  ∀ (L : ℕ) [NeZero L] (n : ℕ) [NeZero n] (g κ E : ℝ) (m : ℂ), 3 ≤ n → BAReal d L g κ E m →
    ∀ (F : Finset (Fin n × Fin n)), KLIsTSP F → ∀ (σ : Fin n → Bool) (a : Fin n → Zd d L) (t : ℝ), 0 ≤ t → t < 1 →
      HasDerivAt (fun s : ℝ => BAGamma d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) s F σ a)
        (BAGammaDerivRHS d L n g E m t F σ a) t
def BALeafPairsStmt (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] (g κ E : ℝ) (m : ℂ), BAReal d L g κ E m →
    ∀ K : ℝ → LoopIdx (Zd d L) → ℂ, BASplicedFam d L W g E m K →
    ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ (σ : Fin n → Bool) (a : Fin n → Zd d L) (t : ℝ), 0 ≤ t → t < 1 →
      (((W : ℂ) ^ d)⁻¹) ^ (n - 1) * ∑ F ∈ TSP n, ∑ v : Fin n, ∑ b : Zd d L,
          (BATheta d L g E m t (σ v) (σ (v + 1)) * BAMss d L (BAMB d L g (E : ℂ) m) (σ v) (σ (v + 1))) (a v) b *
            BAGamma d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t F σ (Function.update a v b)
        = ∑ v : Fin n, ((W : ℂ) ^ d) * ∑ x : Zd d L,
            K t (LoopIdx.cutGlueL (if v.val + 1 < n then v.val + 1 else 1) (if v.val + 1 < n then v.val + 2 else n) x
              (KLloopOf d L σ a)) *
            K t (LoopIdx.cutGlueR (if v.val + 1 < n then v.val + 1 else 1) (if v.val + 1 < n then v.val + 2 else n) x
              (KLloopOf d L σ a))
```
**5. Compiled nonempty instances (file lines 536-566 and 583-598, blank and docstring lines dropped).  Also compiled in the file: `n = 4`, `F = {(0,2)}` for target 2 (545-553), the three clauses of `BAKcac_spliced` at the data (568-578), the four public list facts (599-608)**
```
$ sed -n '536,566p;583,598p' RBM3D/BA/KTreeDeriv.lean | grep -v '^$' | grep -v '^/--' | grep -v '^`(1,2)`'
example :
    HasDerivAt (fun s : ℝ => BAGamma 3 4 3 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) s ∅
        ![true, true, false] ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0]])
      (BAGammaDerivRHS 3 4 3 P.g0 P.E P.m0 (1 / 2) ∅ ![true, true, false] ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0]])
      (1 / 2) :=
  baGamma_hasDerivAt 3 4 3 P.g0 P.m0.im P.E P.m0 (le_refl 3) P.real ∅ BAKTreeDeriv_isTSP_empty _ _ (1 / 2)
    (by norm_num) (by norm_num)
example :
    HasDerivAt (fun s : ℝ => BAGamma 3 4 4 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) s
        {((0 : Fin 4), (2 : Fin 4))} ![true, true, false, true] ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]])
      (BAGammaDerivRHS 3 4 4 P.g0 P.E P.m0 (1 / 2) {((0 : Fin 4), (2 : Fin 4))} ![true, true, false, true]
        ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]])
      (1 / 2) :=
  baGamma_hasDerivAt 3 4 4 P.g0 P.m0.im P.E P.m0 (by norm_num) P.real _ BAKTreeDeriv_isTSP_F02 _ _ (1 / 2)
    (by norm_num) (by norm_num)
example :=
  baLeafPairs 3 4 2 P.g0 P.m0.im P.E P.m0 P.real (BAKcac 3 4 2 P.g0 P.E P.m0) BAKcac_spliced 3 (le_refl 3)
    ![true, true, false] ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0]] (1 / 2) (by norm_num) (by norm_num)
example :=
  baLeafPairs 3 4 2 P.g0 P.m0.im P.E P.m0 P.real (BAKcac 3 4 2 P.g0 P.E P.m0) BAKcac_spliced 4 (by norm_num)
    ![true, true, false, true] ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]] (1 / 2) (by norm_num)
    (by norm_num)
example : (KLloopOf 1 3 ![true, false, true, true] ![![0], ![1], ![2], ![0]]).cutGlueL 2 3 ![1] =
    KLloopOf 1 3 ![true, false, true, true] (Function.update ![![0], ![1], ![2], ![0]] 1 ![1]) := by decide
example : (KLloopOf 1 3 ![true, false, true, true] ![![0], ![1], ![2], ![0]]).cutGlueR 2 3 ![1] =
    ⟨[false, true], [![1], ![1]]⟩ := by decide
example : (KLloopOf 1 3 ![true, false, true, true] ![![0], ![1], ![2], ![0]]).cutGlueL 1 4 ![1] =
    ⟨[true, true], [![1], ![0]]⟩ := by decide
example : (KLloopOf 1 3 ![true, false, true, true] ![![0], ![1], ![2], ![0]]).cutGlueR 1 4 ![1] =
    KLloopOf 1 3 ![true, false, true, true] (Function.update ![![0], ![1], ![2], ![0]] 3 ![1]) := by decide
```
**6. Name-clash grep (`name=<other files on the branch>/<files on main tip>/<files in ../RBM1D, ../RBM2D>`; 0/0/0 = no clash)**
```
$ for n in BASplicedFam BAGammaDerivRHS BAGammaDerivStmt BALeafPairsStmt baGamma_hasDerivAt baLeafPairs BAKcac BAKcac_spliced KLloopOf_cutGlueL_leaf KLloopOf_cutGlueR_leaf KLloopOf_cutGlueL_wrap KLloopOf_cutGlueR_wrap BAKTreeDeriv_ KTreeDerivInst; do printf "%s=%s/%s/%s  " $n $(grep -rlw "$n" RBM3D --include="*.lean" | grep -v BA/KTreeDeriv.lean | wc -l | tr -d " ") $(git -C /Users/junyin/Lean_proof/RBM3D --no-optional-locks grep -lw "$n" main -- "RBM3D/*.lean" | wc -l | tr -d " ") $(grep -rlw "$n" /Users/junyin/Lean_proof/RBM1D/RBM1D /Users/junyin/Lean_proof/RBM2D/RBM2D --include="*.lean" 2>/dev/null | wc -l | tr -d " "); done; echo; git -C /Users/junyin/Lean_proof/RBM3D --no-optional-locks log -1 --format="main tip %h %cd"
BASplicedFam=0/0/0  BAGammaDerivRHS=0/0/0  BAGammaDerivStmt=0/0/0  BALeafPairsStmt=0/0/0  baGamma_hasDerivAt=0/0/0  baLeafPairs=0/0/0  BAKcac=0/0/0  BAKcac_spliced=0/0/0  KLloopOf_cutGlueL_leaf=0/0/0  KLloopOf_cutGlueR_leaf=0/0/0  KLloopOf_cutGlueL_wrap=0/0/0  KLloopOf_cutGlueR_wrap=0/0/0  BAKTreeDeriv_=0/0/0  KTreeDerivInst=0/0/0  
main tip c0a7747 Fri Oct 9 22:36:48 2026 -0700
```
**7. Registry pre-check (temporary file outside the repository; DECISIONS §181 (2))**
```
$ cat $S/lean/RegistryPrecheck.lean; lake env lean $S/lean/RegistryPrecheck.lean > $S/lean/precheck_out2.txt 2>&1; echo "exit code: $?"; head -2 $S/lean/precheck_out2.txt | cut -c1-150; tail -1 $S/lean/precheck_out2.txt | cut -c1-150; echo "lines naming a new name: $(grep -c "BASplicedFam\|BAGammaDeriv\|BALeafPairs\|KTreeDeriv\|BAKcac" $S/lean/precheck_out2.txt)"
import RBM3D
import RBM3D.BA.KTreeDeriv

#assert_rbm_axioms
exit code: 0
axiom audit: 10797 theorems, 3175 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
non-vacuity certificates: 0 of 127 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what e
lines naming a new name: 0
```
**8. The C3 table again (`summ.py` over `c3_out.txt`, the preflight run of `c3.py 6`; (a) abs ≤ 1e-8 is the finite-difference limit, (b) ≤ 1e-12, stop line 1e-10)**
```
$ cd $S && python3 summ.py
n  #TSP  (a)abs      (a)rel     (b)leaf    (b)wrap    (c)total   list-identity checks
3     1  2.10e-12  3.08e-13  1.78e-15  1.86e-15  7.11e-15   39360
4     3  3.90e-11  1.15e-12  2.84e-14  2.14e-14  9.95e-14   483840
5    11  1.21e-10  2.66e-12  7.11e-15  4.44e-15  8.88e-15   17280
6    45  9.07e-09  5.36e-11  4.10e-14  7.11e-14  1.85e-13   41472
matrix-level max over 9 configs: dTheta=4.4e-13 resolvent=4.4e-16 commute=4.4e-16 symm=3.3e-16 swap=4.4e-16 dTT=3.0e-13
```
**9. Diff against main (only the new file), worktree clean**
```
$ git diff --stat main...t/T2370; git status --short | wc -l
 RBM3D/BA/KTreeDeriv.lean | 612 +++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 612 insertions(+)
       0
```
**Narrative.** Stage 1b, role `prover-max` (ticket), resumed under rule (H) from a clean worktree at d78b09f (first tool call: `git log`, `git status --short` empty).
- All four targets are built in the one new file `RBM3D/BA/KTreeDeriv.lean` (612 lines, 6 commits; `wc -l` 285 / 417 / 513 / 603 / 612 / 612 at the commits, block 1, the last one changes docstrings only; the stop line 2000 was never near; the 1a plan said central ≈ 1265, low 800). No new hypothesis, no pin changed, no amend, no REQ. Pins are textually the check file's (block 3); axioms standard (block 2); registry pre-check exit 0 (block 7).
- Target 2, `baGamma_hasDerivAt`: `BAKTreeDeriv_gval_hasDerivAt` is the `KLgval` form of `KLhasDerivAt_treeValW` (`Loop/KLCut.lean:178-202`, same proof with `KLprod_update_eq`); `BAKTreeDeriv_gval_leaf_mul` the `KLgval` form of `treeValW_leaf_mul` (`Loop/KLTreeDeriv.lean:168-184`). Leaf `v`: `BATheta_hasDerivAt` with `ΘMΘ = (ΘM)·Θ`, leaf_mul, and `Function.update_eq_self` (the weight being replaced is `Θ`). Chord: `HasDerivAt.ofReal_comp` and `HasDerivAt.mul` on `r ↦ r·Θ_r`, then `BAKTreeDeriv_ThetaSq` (`ΘΘ = Θ + tΘMΘ`: the first conjunct `Θ = 1 + tMΘ` of `BATheta_resolvent` multiplied by `Θ` on the left). `M`-edges: constant (`hasDerivAt_const`), their terms carry a zero weight and vanish (`BAKTreeDeriv_gval_zero_edge`; edge sum split by `Fintype.sum_sum_type`). The pin's `3 ≤ n` and `KLIsTSP F` are not used by the proof: the formula holds for every `F` and `n`.
- Target 3, `baLeafPairs`: the per-`v` identity `hv` by cases on `v.val + 1 < n`. Leaf pair: `KLloopOf_cutGlueL_leaf` (n-loop, clause 3 of `K`) and `KLloopOf_cutGlueR_leaf` (2-loop `⟨[σ_v,σ_{v+1}],[a_v,x]⟩`, clause 2, the closed form, never `BAGamma` at `n = 2`). Wrap pair: `KLloopOf_cutGlueL_wrap` (2-loop `⟨[σ_0,σ_{n-1}],[x,a_{n-1}]⟩`) and `KLloopOf_cutGlueR_wrap`. The scalar `W^d (W^d)⁻¹ (W^d)⁻¹^{n-1} = (W^d)⁻¹^{n-1}` holds also at `W^d = 0` (`BAKTreeDeriv_scalar`, `n - 1 ≠ 0`), so no `0 < W` is needed.
- Wrap reversal (C2), `BAKTreeDeriv_P_swap`: `BAMss B s' s = (BAMss B s s')ᵀ` for every `B` (`BAKTreeDeriv_Mss_swap`: unfold `BAMss`, `mul_comm`); `Ring.inverse` commutes with `ᵀ` (`BAKTreeDeriv_Theta_swap`); `ΘQ = QΘ` from the two resolvent identities, split `t = 0` / `t ≠ 0` (`BAKTreeDeriv_Theta_comm`). It uses neither `BATheta_swap`, `BATheta_isSymm` nor `BAMB_symm`, hence no symmetry of `M(σ)` (route of 1a-audit O1); hypotheses `BAReal`, `0 ≤ t < 1`.
- Target 4: `BAKcac` is an `if` chain on `I.σ.length = I.a.length` and `I.a.length ∈ {1, 2, ≥ 3}`; clauses 1-2 of `BAKcac_spliced` by `simp [BAKcac]`; clause 3 through `BAKTreeDeriv_Kcac_eq` (`subst` of the length; `NeZero` is a `Prop`, so the instance built inside the definition is the given one) and `BAKTreeDeriv_getD_ofFn`.
- The list facts are proved by `List.ext_getElem` with `simp` and `omega`; `KLloopOf_cutGlueL_leaf` needs no hypothesis on `v` (the hypothesis `v + 1 < n` of commit 2864401 was unused and is dropped in 7422664).
- Instances (block 5): `P : FlowPt 4 10` (`BA/MFixedPoint.lean:893`), `W = 2`, `t = 1/2`; `n = 3` (`TSP 3 = {∅}`, checked by `decide` in a scratch file) and `n = 4` (`TSP_four`: three trees), `BAReal` by `P.real`, `KLIsTSP` by a direct proof for `F = ∅` and by `KLisTSP_of_mem_TSP` for `F = {(0,2)}`, `BASplicedFam` by `BAKcac_spliced`; four list identities at `n = 4` by `decide`.
- No port from `../RBM1D` or `../RBM2D` (they were only grepped for name clashes, block 6); the proofs are adapted from the merged RBM3D files named above, so there is no RBM1D/RBM2D diff-stat.

## (c) Verified Mathlib/core names used (all `#check`ed, 0 errors; `KTreeDeriv.lean` first-use lines in brackets)
- `HasDerivAt.fun_sum` [167]: `(∀ i ∈ u, HasDerivAt (A i) (A' i) x) → HasDerivAt (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x`
- `HasDerivAt.fun_finsetProd` [168]: derivative `∑ i ∈ u, (∏ j ∈ u.erase i, f j x) • f' i`, needs `[DecidableEq ι]`
- `HasDerivAt.mul` [239]: `HasDerivAt (c * d) (c' * d x + c x * d') x` for `c d : 𝕜 → 𝔸`
- `HasDerivAt.ofReal_comp` [239]: `HasDerivAt f u z → HasDerivAt (fun y => ↑(f y)) (↑u) z` for `f : ℝ → ℝ`
- `HasDerivAt.congr_deriv`, `hasDerivAt_id` [239], `hasDerivAt_const` [257]
- `Fintype.sum_sum_type` [280]: `∑ x, f x = ∑ a₁, f (Sum.inl a₁) + ∑ a₂, f (Sum.inr a₂)`
- `Function.update_eq_self` [273]: `Function.update f a (f a) = f`; also `Function.update_self`, `Function.update_of_ne`, `Function.update_apply`
- `Finset.prod_eq_zero`, `Finset.sum_eq_zero`, `Finset.sum_comm`, `Finset.mul_sum`, `Finset.sum_mul`, `Finset.sum_add_distrib`
- `Matrix.nonsing_inv_eq_ringInverse` [121]: `A⁻¹ = Ring.inverse A`; `Matrix.transpose_nonsing_inv` [122]: `A⁻¹ᵀ = Aᵀ⁻¹`
- `Matrix.transpose_mul` [144], `Matrix.transpose_sub`, `Matrix.transpose_one`, `Matrix.transpose_smul`, `Matrix.mul_smul`, `Matrix.mul_assoc`
- `smul_right_injective` [136]: `r ≠ 0 → Function.Injective fun x => r • x` (needs `Module.IsTorsionFree`)
- `List.set_eq_take_append_cons_drop` [294]: `l.set i a = if i < l.length then take i l ++ a :: drop (i+1) l else l`
- `List.ext_getElem` [298], `List.getElem_ofFn`, `List.getElem_set`, `List.getElem_append_left`, `List.getElem_append_right`, `List.getElem_drop`, `List.take_append_drop`
- `List.getD_eq_getElem?_getD` [397]: `l.getD i a = l[i]?.getD a`
- `Fin.val_add`, `Fin.val_one'`, `Nat.mod_eq_of_lt`, `Nat.mod_self` [318, 494]; `mul_inv_cancel₀`, `zero_pow` [431-432]
- Verified absent (`#check`: unknown constant; `grep` over `Mathlib/` finds none): `List.ofFn_update`, `List.set_ofFn`, `List.ofFn_set`
- Deprecated in this toolchain (tool log, Lean 4.34.0): `if_pos`, `if_neg`, `dif_pos` (use `simp only [h, ↓reduceIte, ↓reduceDIte]`); a `show` that changes the goal triggers `linter.style.show` (use `change`)

## (d) Open issues and paper-delta candidates
- `T2370a` (from (a)): `baLeafPairs` takes `W : ℕ` with no `0 < W`; the identity holds also at `W^d = 0` (both sides are `0`, `n - 1 ≥ 2`).
- No other Lean/paper difference arose. Read against `A:552-583`: leaf `Θ^{(σ_k,σ_{k+1})}` (`f-external2`, cyclic), chord `tΘ^{(σ_k,σ_l)}` (`f-internal2` at `S^{(B)} = I`: D633), `n ≥ 3` (D634), `(Kn2sol)` (`1_2:1175`) as clause 2 of `BASplicedFam`. `tree-representation_BA` stays a gap in the TeX (design §3 (a)); the derivative identities of K05 are now compiled.
- For K05b (not in this ticket): the chord pairs `(i+1, j+1)` through `KLsum_cut` and `IsKLoopS` for `BAKcac`. Block 8, column (c): leaf plus chord parts against the whole `treeEqRhsS` agree to 1.85e-13 for `n ≤ 6`.
- Size datum for the Q4 evaluation (supervisor 0350 C5): K05a's line count is 612.
- `BAKcac` is `0` on `σ.length ≠ a.length`, which is a choice of the Lean definition, not a paper statement (`IsKLoopS` ignores such indices).
