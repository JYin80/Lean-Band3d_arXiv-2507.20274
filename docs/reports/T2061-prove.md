Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 18:55:29 UTC 2026

Sources read at RBM2D `c9a24cf` (`git show c9a24cf:RBM2D/Green/{CondRow,GreenDeriv,FlucVanish}.lean`: 492, 418, 556 lines).
RBM3D: `RBM3D/Defs/{Block,Sizes,Neighbours}.lean`, `RBM3D/Gauss/FineModel.lean`, `RBM3D/Green/{EntryCore,EntryDom,RowIndep}.lean`; paper `paper/tex/1_2_Intro_model_result.tex:303-306` (`eq:variancematrix`).

### (i) Exponent table (every `d = 2` token of FlucVanish; counts by `grep -o` on the c9a24cf source: `W ^ 2`/`W²` 8, `W⁻²`-type 7, `Z2` 14 (= portmap 14), `d = 2` 3, `sbSupport` 29)

| RBM2D declaration (FlucVanish line) | d = 2 token | d >= 3 replacement | why it holds | verdict |
|---|---|---|---|---|
| `flucVanish_card_filter_blk2_mem` (350) | `Finset (Z2 L)`, count `T.card * W^2`, via `Fin W × Fin W` and `sq` | `Finset (Zd d L)`, `T.card * W^d`; fibre is `Fin (W^d)` directly (`splitEquiv : Idx d L W ≃ Vtx d L W = Zd d L × Fin (W^d)`), no `sq` | `Fintype.card (Fin (W^d)) = W^d`; `splitEquiv` bijective (`Defs/Sizes.lean`, `split_bijective`) | PASS |
| `flucVanish_card_blockSupport` (419) | `W^2` sites per block | `W^d` (`card_Iblk`, `Defs/Sizes.lean`) | same | PASS |
| `uniformWeight_blockAvg2` (456) | weight `(W⁻¹)^2`, mass `W⁻² · W² = 1` | weight `((W:ℝ)^d)⁻¹`, mass `((W:ℝ)^d)⁻¹ · W^d = 1` (`sum_abs_blkCoef2`, `EntryDom.lean`: `∑ |blkCoef2| = 1`) | block has `W^d` sites each of weight `W^{-d}` | PASS |
| `flucVanish_blockAvg2_eq_blkCoef2` (472, **target**) | `(W⁻¹)^2`, `Z2 L` | `((W:ℝ)^d)⁻¹`, `Zd d L`; RHS `blkCoef2 d L W a (splitEquiv d L W k)` (`EntryDom.lean:484`: `if k.1 = a then (W^d)⁻¹ else 0`) | definitional (`rfl` in RBM2D; blocks of `k` = `(split k).1` = `(splitEquiv k).1`) | PASS |
| `flucVanish_card_filter_sub_mem_sbSupport` (374), `flucVanish_card_sbSupport_le` (388, `<= 5`), `flucVanish_card_svarSupport` (400), `..._eq` (412, `5 W^2`) | five-point `sbSupport L` | no `sbSupport` in RBM3D; support of `sbKernelR d L g` is `{0} ∪ {x : zdistD x = 1}`, `1 + 2d` points for `3 <= L` (`card_nbhd`, `Defs/Neighbours.lean:158`) and only when `g ≠ 0` (else `{0}`) | row support `(2d+1) W^d` | PASS (rewritten, constant `5 -> 2d+1`, needs `g ≠ 0` for equality) |
| `uniformWeight_svar` (428) | `UniformWeight (svar i ·) ((5)⁻¹ (W⁻¹)^2) A`: `t = c` on the whole support | **no uniform replacement**: `svarF d L W g i j = (W^d)⁻¹ · sbKernelR d L g (a-b)`, value `W^{-d}/(1+2dg²)` if same block, `W^{-d} g²/(1+2dg²)` if neighbouring block (`Block.lean:32-37,74-76`; paper `eq:variancematrix`) | two different values on the support unless `g² = 1`; RBM2D `svar` is a **fixed uniform** five-point profile (`Gauss/Model.lean:42-44` at c9a24cf: `if … ∈ sbSupport L then 5⁻¹ W⁻² else 0`, no `g`) | **FAIL as ported** |
| docstring/`Checks` (`L=3,W=2`, support 20 = 5·4, `1/20`) | numeric d = 2 | not ported (checks are re-done at `d = 3` instance) | — | n/a |

`Σ_b |S_ab| = 1`: `sum_sbKernelR` (`Defs/Block.lean:93`, `3 <= L`, `a + 2d·g²a = 1`); on the fine lattice `Σ_j svarF i j = W^d · W^{-d} · 1 = 1`. This is the mass bound a weight family can still satisfy (script below: row sum 1.0).

Exponent/constant rows the targets depend on:

| quantity | value (d = 3) | constraint | slack |
|---|---|---|---|
| block size `W^d` | 8 at `W=2` | `blkCoef2` weight `(W^d)⁻¹`, `Σ = 1` | exact equality |
| `N = (W L)^d` | 512 at `L=4, W=2` | `Fintype.card (Idx d L W)` (`card_Idx`) | exact |
| `3 <= L` | `L = 4` | `sum_sbKernelR`, `card_nbhd` | slack 1 |
| row support (true) | `(2d+1) W^d = 56` (g=1/2) | needs `g ≠ 0`, `3 <= L` | — |
| row max entry (true) | `W^{-d}/(1+2dg²) = 0.05` | `<= W^{-d} = 0.125` | factor 2.5 |
| uniform `c` claimed by port | `1/((2d+1)W^d) = 0.017857` | row values are `0.05` and `0.0125` | **violated** (`mem` fails) |
| `CondRow` / `GreenDeriv` | no `W`, `L`, `d` exponent (portmap row 29 `-`; row 43 only `Z2` in docstring/check) | index type `Idx (L n) (W n)` -> `Idx d (sz.L n) (sz.W n)`; coordinates `CoordF d L W` | — |

### (ii) One concrete nondegenerate instance: `d = 3, L = 4, W = 2, g = lam = 1/2, u = t = 1/2, z = 1/2 + i/2`

Model as in `FineModel.lean` (`Hflow u ω = √u • Xmat ω`, `gvarF` = `S_ii` on the diagonal, `S_ij/2` per real part off it, `Xentry`), `S^(B)(g)` as `sbKernelR`. Hypotheses of the targets: `greenMinorMat_eq_minorGreen`: `IsUnit det(H_u - z)`, `G_kk ≠ 0` (both hold: `z.im ≠ 0`, `H` Hermitian); `continuous_green_comp`: `f` continuous Hermitian, `z.im ≠ 0` (instance `f = u ↦ √u X`; no external hypothesis, so no limit computation beyond the continuity check below); `flucVanish_blockAvg2_eq_blkCoef2`: `NeZero L, NeZero W` only.

Command: `python3 scratchpad/T2061/check.py` (numpy; scratchpad `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2061/check.py`; Python only, no Lean). Output, verbatim:

```
N = 512 Hermitian: True
det unit: |det(H-z)|^(1/N) = 0.840128234805198  |G_kk| = 1.0003715371809798
greenMinorMat vs minorGreen: max entry diff = 4.285518399176076e-15  max |entry| = 1.2583465217185599
h=0.001: ||G_(u+h)-G_u|| = 2.412e-03 <= ||H(u+h)-H(u)||/eta^2 = 5.705e-03
h=1e-06: ||G_(u+h)-G_u|| = 2.414e-06 <= ||H(u+h)-H(u)||/eta^2 = 5.708e-06
blockAvg2 vs blkCoef2: mismatches 0 of 32768
split injective: True | #block a0 = 8 = W^d = 8
sum_k blockAvg weight = 1.0
row sum S_ij = 1.0 | distinct row values: [np.float64(0.0), np.float64(0.0125), np.float64(0.05)] | support size 56 = (2d+1)W^d = 56
uniform c would be 1/((2d+1)W^d) = 0.017857142857142856 ; max entry = 0.05 <= W^-d = 0.125
2D-style claim (5W^2)^-1 = 0.05
```

Reading: line 3 = both sides of `greenMinorMat_eq_minorGreen` (minor-inverse vs `G_ij - G_ik G_kj / G_kk`) agree to `4e-15` at `k = (3,5,6)`; lines 4-5 = continuity of `t ↦ G_t` (resolvent identity bound `‖ΔG‖ <= ‖ΔH‖/η²`, `η = 1/2`); line 6 = both sides of `flucVanish_blockAvg2_eq_blkCoef2` over all `64 · 512` pairs `(a, k)`; the last three lines show the row profile `t_j = S_{0j}` takes two nonzero values, so `UniformWeight` (equality `t = c` on the support) fails.

### Verdict per target

* `greenMinorMat_eq_minorGreen` (CondRow:358): **PASS**. Dimension-free linear algebra (`inv_minor_resolvent`, `EntryCore.lean:233`, exists); only the index type changes. Needs `FinDepOffRow`/`rowSplit`/`condRow` ported (none exists in RBM3D: grep over `RBM3D/` finds only docstring mentions), reusing `rowSet`, `offRowCoord`, `Hflow_submatrix_congr_offRowCoord` (`RowIndep.lean:336,588,609`).
* `continuous_green_comp` (GreenDeriv:354): **PASS**. `d`-free; the body is `continuous_green_of_isHermitian` (`Gauss/FlowCalculus.lean:191`, exists).
* `flucVanish_blockAvg2_eq_blkCoef2` (FlucVanish:472): **PASS** (table row above; instance mismatches 0 of 32768).
* Non-key public declarations `uniformWeight_svar` (428), and the support-count lemmas it rests on (`flucVanish_card_sbSupport_le`, `..._card_svarSupport`, `..._eq`): **FAIL** as ported at `d >= 3`: `UniformWeight` requires `t k = c` on `A` (`mem`) and `0` off it, but the 3D row `j ↦ svarF d L W g i j` has the two values `W^{-d}/(1+2dg²)` and `g² W^{-d}/(1+2dg²)` on `A` (output above: 0.05 and 0.0125 vs. claimed 0.017857). It is true only at `g² = 1` (`c = ((2d+1) W^d)⁻¹`), and `lam` is a sequence that may tend to `0` (`Sizes.lam`, `Defs/Sizes.lean`; `(eq:WO)`). ST1-COMMON item 6/ticket: statement false at `d >= 3` as ported, stop and report.
  Consumers in RBM2D (found by `git grep` at c9a24cf): `FlucAvg.lean:348-370`, `FlucAvgDet.lean:168,233,305,474,590` (hypothesis `UniformWeight (Tw n a) (cw n) (Aw n a)`), `FlucIter.lean:967-1024,1458,1630` (S1-18, S1-20, S1-30). Dispatcher decision needed. Options (not decided here): (A) in this ticket, replace the row family by a **bounded-weight** statement `0 <= t k <= c = W^{-d}` on `A = {j : (a_i - a_j) ∈ {0} ∪ nbhd}` (`#A = (2d+1) W^d` for `g ≠ 0`), `t = 0` off `A`, `Σ t = 1`, all true at `d >= 3` (checked numerically above); the RBM2D proof at `FlucIter.lean:980-995` evaluates `∏|t(v i)|` through `|t (v i)| = c`, where `<= c` would suffice, other uses unchecked; this changes the structure `UniformWeight` (field `mem` becomes `<=`), hence downstream tickets; (B) keep `UniformWeight` unchanged, drop `uniformWeight_svar` here and let S1-18 decide the row family. The key target `flucVanish_blockAvg2_eq_blkCoef2` and `uniformWeight_blockAvg2` are unaffected (block average is uniform at all `d`).

Overall verdict: **FAIL** (hypothesis-free statement `uniformWeight_svar` false at `d >= 3` as ported; the three key targets pass).


## (a) Math preflight — round 2 under Amend 1 (BoundedWeight) — Sat Oct  3 19:15:13 UTC 2026

Round-1 rows above stand except the rows `uniformWeight_svar`, the support-count lemmas and the `UniformWeight` verdict, which are redone here. Sources: `git -C ../RBM2D show c9a24cf:RBM2D/Green/{FlucVanish,FlucIter,FlucAvgDet}.lean`; `RBM3D/Gauss/FineModel.lean:47` (`svarF`), `Propagator/Props4.lean:48` (`SBR`), `Defs/Block.lean` (`sbKernelR`, `sum_sbKernelR`), `Defs/Neighbours.lean:158` (`card_nbhd`), `Green/RowIndep.lean:1520` (`sum_svarF_row`, **private**).

### (i) Exponent table (rows changed by the amend)

What the RBM2D consumers use of `UniformWeight t c A` (grep of `hw` in FlucIter/FlucAvgDet at c9a24cf): `hw.nonneg`, `hw.mem` (`|t k| = c`, FlucIter 980-995, to evaluate `∏|t(v i)|`), `hw.not_mem` (FlucIter 991), and `hw.mass : c * #A ≤ 1` (FlucIter 1018, `pow_le_one₀` on `(c #A)^s`). FlucAvgDet only passes `hw` through. So the consumers do use a mass bound; for the 3D row `c · #A = W^{-d} (2d+1) W^d = 2d+1 > 1`, so `mass` cannot be kept in the form `c * #A ≤ 1`.

| item | value / statement | constraint | why it holds / slack |
|---|---|---|---|
| `BoundedWeight t c A` fields | `0 ≤ c`; `∀ k, 0 ≤ t k`; `∀ k ∈ A, t k ≤ c`; `∀ k ∉ A, t k = 0`; **`∑ k, t k ≤ 1`** (`sum_le`) | the sum field replaces `mass`; it is "≤ 1", not "= 1", because `UniformWeight` only gives `∑ t = c #A ≤ 1` | the `0 ≤ c` field is needed for `toBoundedWeight` (`UniformWeight.nonneg`), not derivable from `t ≤ c` when `A = ∅` |
| `UniformWeight.toBoundedWeight` | `t = c` on `A`, `0` off `A`, `c #A ≤ 1` ⇒ all five fields | `∑ t = ∑_{k∈A} c = c #A ≤ 1` | exact; no slack needed |
| `uniformWeight_blockAvg2` (unchanged) | `c = (W^d)⁻¹`, `A` = block `a`, `#A = W^d`, `c #A = 1` | `UniformWeight` kept; `∑ = 1` (`sum_blkCoef2`, `EntryDom.lean:507`) | equality 1 = 1 |
| `boundedWeight_svarF` row `t j = svarF d L W g i j` | `c = (W^d)⁻¹`, `A = {j : blk i − blk j = 0 ∨ zdistD(blk i − blk j) = 1}` (equivalently `blk j − blk i`, by `sbKernelR_neg`) | `3 ≤ L` for `sum_sbKernelR`, `card_nbhd` | see next rows |
| `0 ≤ t j` | `svarF_nonneg` (exists) | `g` arbitrary real | `W^{-d} ≥ 0`, `sbKernelR ≥ 0` |
| `t j ≤ c` on `A` | `t j = W^{-d} sbKernelR(x)`, `sbKernelR x ∈ {(1+2dg²)⁻¹, g²(1+2dg²)⁻¹}` on `A` | need `sbKernelR x ≤ 1` | `(1+2dg²)⁻¹ ≤ 1`; `g²/(1+2dg²) ≤ 1/(2d) ≤ 1`; slack at `g=1/2`: `0.05 ≤ 0.125` (factor 2.5); at `g=1`: factor 7; `g=2`: factor 6.25 (script) |
| `t j = 0` off `A` | `sbKernelR x = 0` unless `x = 0` or `zdistD x = 1` | definition | exact; also holds for `g = 0` (support only shrinks) |
| `∑ j, t j ≤ 1` | `= 1` | `sum_svarF_row` is private in RowIndep ⇒ re-prove in the new file: `splitEquiv`, `W^d · (W^d)⁻¹ = 1`, `sum_sbKernelR` | equality 1 = 1; script: sum 1 at all `g` |
| `#A` | `(2d+1) W^d` (`d=3,W=2`: 56) | `3 ≤ L` so the `2d` unit neighbours are distinct (`card_nbhd`: `#{zdistD x = 1} = 2d`) and `0` is not one of them (`zdistD 0 = 0 ≠ 1`); each block has `W^d` sites (`card_Iblk`) | exact, independent of `g` (`A` is geometric); `supp t = A` iff `g ≠ 0` |
| support-count lemmas (port) | `flucVanish_card_svarSupport` ⇒ `#A = #{b : blk i − b ∈ {0}∪nbhd}·W^d`; `flucVanish_card_sbSupport_le (≤5)`, `_svarSupport_eq (=5W²)` become `= 2d+1`, `= (2d+1)W^d` | as above | RBM2D 5 = 1 + 2·2 is exactly `2d+1` at `d=2` |
| `flucVanish_blockAvg2_eq_blkCoef2`, `greenMinorMat_eq_minorGreen`, `continuous_green_comp` | unchanged from round 1 | — | PASS (round 1) |

Downstream (S1-18, not this ticket): `sum_prod_abs_card_image_le` with `mass` replaced by `∑ t ≤ 1`. Hand check: for `v` with image set `S`, `|S| = m ≤ s`, `∏_i t(v i) ≤ c^{n-m} ∏_{u∈S} t u`, hence the stratum sum is `≤ c^{n-m} m^n (∑ t)^m ≤ c^{n-m} m^n`; since `c ≤ 1`, summing `m ≤ s` gives `≤ s · c^{n-s} s^n`, i.e. at most the factor `s ≤ n` more than the RBM2D constant. The script below shows the RBM2D constant `c^{n-s} s^n` itself holds at `n = 2,3,4`. The hypothesis `2p ≤ #A` becomes `2p ≤ (2d+1) W^d` (true for `W` large), `c ≤ ρ²` becomes `W^{-d} ≤ ρ²`.

### (ii) Concrete instance: `d = 3, L = 4, W = 2` (`N = 512`), row of `i` at block `(0,0,0)`, `g ∈ {1/2, 1, 2}`, exact rational arithmetic

Round-1 numeric lines (both sides of `greenMinorMat_eq_minorGreen` at `t = u = 1/2`, `flucVanish_blockAvg2_eq_blkCoef2`) are unchanged by the amend. New command (Python `fractions`; no Lean): `python3 scratchpad/T2061/check2.py` (file `/Users/junyin/Lean_proof/RBM3D`-independent: `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2061/check2.py`). Output, verbatim:

```
#A = 56 (2d+1)W^d = 56 | c = W^-d = 1/8
g=1/2: nonneg=True t<=c on A=True t=0 off A=True sum=1 values=[0.0, 0.0125, 0.05] max/c=0.4
   strata: n=2,s=1: 0.02750 <= 0.12500: True | n=3,s=2: 0.08031 <= 1.00000: True | n=4,s=2: 0.006337 <= 0.250000: True
   UniformWeight.mass field c*#A = 7.0 (<=1? False); with c=1/((2d+1)W^d): mem holds? False
g=1: nonneg=True t<=c on A=True t=0 off A=True sum=1 values=[0.0, 0.017857142857142856] max/c=0.14285714285714285
   strata: n=2,s=1: 0.01786 <= 0.12500: True | n=3,s=2: 0.05293 <= 1.00000: True | n=4,s=2: 0.002198 <= 0.250000: True
   UniformWeight.mass field c*#A = 7.0 (<=1? False); with c=1/((2d+1)W^d): mem holds? True
g=2: nonneg=True t<=c on A=True t=0 off A=True sum=1 values=[0.0, 0.005, 0.02] max/c=0.16
   strata: n=2,s=1: 0.01940 <= 0.12500: True | n=3,s=2: 0.05743 <= 1.00000: True | n=4,s=2: 0.002623 <= 0.250000: True
   UniformWeight.mass field c*#A = 7.0 (<=1? False); with c=1/((2d+1)W^d): mem holds? False
UniformWeight example: sum = 1 <= 1 :  True
```

Reading: `#A = 56 = (2d+1)W^d`; for every `g`: `t ≥ 0`, `t ≤ c = 1/8` on `A`, `t = 0` off `A`, `∑ t = 1`, two nonzero values (`g ≠ 1`) or one (`g = 1`). The `mass` field `c · #A = 7 > 1` fails at every `g` (so `BoundedWeight` must carry `∑ t ≤ 1`), and `UniformWeight`'s `mem` with `c = ((2d+1)W^d)⁻¹` fails for `g ≠ 1` (round-1 FAIL confirmed). External hypotheses: none (all rows are deterministic; no limit computation needed).

### Verdict per target (amended ticket)

* `greenMinorMat_eq_minorGreen` (CondRow:358): **PASS** (round 1, unchanged).
* `continuous_green_comp` (GreenDeriv:354): **PASS** (round 1, unchanged).
* `flucVanish_blockAvg2_eq_blkCoef2` (FlucVanish:472): **PASS** (round 1, unchanged).
* `uniformWeight_blockAvg2`, `UniformWeight.toBoundedWeight`: **PASS**.
* `boundedWeight_svarF` and its support counts (`#A = (2d+1) W^d`): **PASS**, provided `BoundedWeight` has the five fields above (in particular `0 ≤ c` and `∑ t ≤ 1`, not `c #A ≤ 1`); `sum_svarF_row` must be re-proved (private in RowIndep).

Overall verdict: **PASS**.

## (a′) Preflight corrections — Sat Oct  3 19:48:39 UTC 2026

* Round 1 cites `flucVanish_card_svarSupport` at FlucVanish:400; it is at line 398 of c9a24cf (b.6).
* Round 1 says the body of `continuous_green_comp` is `continuous_green_of_isHermitian` (`Gauss/FlowCalculus.lean:191`); that lemma is stated for `Gres (f v) z true`, so the port adds the conversion `Gres H z true = green H z`.
* Round 1 says `IsUnit det` and `G_kk ≠ 0` hold at every sample: true, but the Lean proof of `G_kk ≠ 0` needs RBM2D `Green/LDE.lean:35-100` (S1-18, not merged): a private port is in the file. None of these changes a verdict.

## (b) Script output — Sat Oct  3 19:48:39 UTC 2026

### b.1 Build, full library, registry pre-check, imports (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2061`, branch `t/T2061`)

```
$ lake build RBM3D.Green.FlucVanish 2>&1 | grep "warning: RBM3D/Green/FlucVanish"; ... | tail -1
warning: RBM3D/Green/FlucVanish.lean:1004:0: `prod_epsHom_sum_eq` does not use the following hypothesis in its type:
Build completed successfully (3330 jobs).
$ lake build RBM3D.Test.Axioms 2>&1 | tail -1; lake build 2>&1 | tail -1
Build completed successfully (2 jobs).
Build completed successfully (3782 jobs).
$ scratch registry_precheck.lean = `import RBM3D` / `import RBM3D.Green.FlucVanish` / `#assert_rbm_axioms`; lake env lean registry_precheck.lean > reg.out; echo exit=$?; head -1 reg.out; grep "premises found" reg.out
exit=0
axiom audit: 2262 theorems, 905 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 47 (borrowed 2, owed 32, structural 13).
$ python3 scratch/imports.py
direct imports of Green/FlucVanish.lean: Gauss.FlowCalculus Green.EntryCore Green.EntryDom Green.LDEQuad Green.RowIndep Hierarchy.ContractionBasic
transitive modules: 46 with the four ticket modules only, 48 with FlucVanish; added: Gauss.FlowCalculus Hierarchy.ContractionBasic
$ git diff --stat main...t/T2061; git status --short | wc -l
 RBM3D/Green/FlucVanish.lean | 1613 +++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean      |    1 +
 2 files changed, 1614 insertions(+)
       0
$ grep -cE 'sorry|admit|native_decide|axiom' RBM3D/Green/FlucVanish.lean
0
```

### b.2 `#print axioms` of every public declaration (116: 97 in `RBM.Green`, 19 in `RBM.Green.FlucVanishInst`)

```
$ python3 scratch/axioms_gen.py; lake env lean scratch/axioms_check.lean > axioms_out.txt; python3 scratch/axioms_summary.py | head -5
#print axioms lines: 116 | declarations with an axiom outside {propext, Classical.choice, Quot.sound}: 0
'RBM.Green.greenMinorMat_eq_minorGreen' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.continuous_green_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.flucVanish_blockAvg2_eq_blkCoef2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.boundedWeight_svarF' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### b.3 Target statements, extracted from the file by script (`python3 scratch/extract.py stmt <name>`; line = line in `RBM3D/Green/FlucVanish.lean`)

```
346: theorem greenMinorMat_eq_minorGreen (sz : Sizes d) (n : ℕ) (u : ℝ) (z : ℂ) (k : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) (hdet : IsUnit (Sizes.seqHflow sz n u ω - z • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)).det) (hGkk : green (Sizes.seqHflow sz n u ω) z k k ≠ 0) : greenMinorMat sz n u z k ω = minorGreen (green (Sizes.seqHflow sz n u ω) z) k
678: theorem continuous_green_comp {V : Type*} [TopologicalSpace V] {f : V → Matrix n n ℂ} (hf : Continuous f) (hherm : ∀ v, (f v).IsHermitian) {z : ℂ} (hz : z.im ≠ 0) : Continuous fun v => green (f v) z
1262: theorem flucVanish_blockAvg2_eq_blkCoef2 (a : Zd d L) (k : Idx d L W) : (if (split d L W k).1 = a then ((W : ℝ) ^ d)⁻¹ else 0) = blkCoef2 d L W a (splitEquiv d L W k)
1169: theorem boundedWeight_svarF (hL : 3 ≤ L) (g : ℝ) (i : Idx d L W) : BoundedWeight (fun j : Idx d L W => svarF d L W g i j) (((W : ℝ) ^ d)⁻¹) ((univ : Finset (Idx d L W)).filter fun j => (split d L W j).1 - (split d L W i).1 ∈ flucVanish_sbSupport d L)
954: theorem UniformWeight.toBoundedWeight [Fintype κ] {t : κ → ℝ} {c : ℝ} {A : Finset κ} (h : UniformWeight t c A) : BoundedWeight t c A
941: structure BoundedWeight [Fintype κ] (t : κ → ℝ) (c : ℝ) (A : Finset κ) : Prop where nonneg_c : 0 ≤ c nonneg : ∀ k, 0 ≤ t k le : ∀ k ∈ A, t k ≤ c not_mem : ∀ k ∉ A, t k = 0 sum_le : ∑ k, t k ≤ 1
```

### b.4 Compiled nonempty instances (same file, namespace `RBM.Green.FlucVanishInst`; `sz0` = `SizesInst.sz0`: d=3, L=4, W=32, lam=1/64, N=2097152)

```
$ python3 scratch/extract.py proof greenMinorMat_eq_minorGreen_sz0 continuous_green_comp_sz0_time flucVanish_blockAvg2_eq_blkCoef2_sz0 boundedWeight_svarF_sz0   # whitespace joined
1366: theorem greenMinorMat_eq_minorGreen_sz0 (ω : Sizes.SeqΩ sz0) : greenMinorMat sz0 0 (1 / 2) zI (0 : Idx 3 (sz0.L 0) (sz0.W 0)) ω = minorGreen (green (Sizes.seqHflow sz0 0 (1 / 2) ω) zI) 0 := greenMinorMat_eq_minorGreen sz0 0 (1 / 2) zI 0 ω (flucVanish_isUnit_det (Sizes.seqHflow_isHermitian sz0 0 (1 / 2) ω) zI_im) (flucVanish_green_diag_ne_zero (Sizes.seqHflow_isHermitian sz0 0 (1 / 2) ω) zI_im 0)
1498: theorem continuous_green_comp_sz0_time (ω : Sizes.SeqΩ sz0) : Continuous fun u : ℝ => green (Sizes.seqHflow sz0 0 u ω) zI := continuous_green_comp (Sizes.continuous_seqHflow_time sz0 0 ω) (fun u => Sizes.seqHflow_isHermitian sz0 0 u ω) zI_im
1536: theorem flucVanish_blockAvg2_eq_blkCoef2_sz0 (k : Idx 3 (sz0.L 0) (sz0.W 0)) : (if (split 3 (sz0.L 0) (sz0.W 0) k).1 = 0 then (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ else 0) = blkCoef2 3 (sz0.L 0) (sz0.W 0) 0 (splitEquiv 3 (sz0.L 0) (sz0.W 0) k) := flucVanish_blockAvg2_eq_blkCoef2 3 (sz0.L 0) (sz0.W 0) 0 k
1581: theorem boundedWeight_svarF_sz0 : BoundedWeight (fun j : Idx 3 (sz0.L 0) (sz0.W 0) => svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) 0 j) ((((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹) ((Finset.univ : Finset (Idx 3 (sz0.L 0) (sz0.W 0))).filter fun j => (split 3 (sz0.L 0) (sz0.W 0) j).1 - (split 3 (sz0.L 0) (sz0.W 0) 0).1 ∈ flucVanish_sbSupport 3 (sz0.L 0)) := boundedWeight_svarF 3 (sz0.L 0) (sz0.W 0) (sz0.three_le_L 0) (sz0.lam 0) 0
all 19 instance declarations: greenMinorMat_eq_minorGreen_sz0 condRow_greenMinorMat_apply_sz0 X0_not_finDepOffRow_szS condRow_sub_condRow_szS integral_condRow_szS integral_mul_prod_eq_zero_szS norm_flucDiag_le_sz0 continuous_green_comp_sz0_time continuous_green_comp_sz0_sample Xmat_eq_sum_sz0 hasFDerivAt_resH_sz0 finDep_of_Hflow_sz0 flucVanish_blockAvg2_eq_blkCoef2_sz0 flucVanish_blockAvg2_nondegenerate_sz0 uniformWeight_blockAvg2_sz0 boundedWeight_blockAvg2_sz0 boundedWeight_svarF_sz0 boundedWeight_svarF_card_sz0 not_uniformWeight_svarF_sz0
$ lake env lean scratch/irc_repro.lean   # `IsRowCoord szT 0 k c` (d=3, L=3, W=1) vs `IsRowCoord sz0 0 k c` as a theorem statement
irc_repro.lean:12:8: warning: declaration uses `sorry`
irc_repro.lean:13:0: error: maximum recursion depth has been reached
```

### b.5 Name clashes of the new public names (97 outside `FlucVanishInst`)

```
$ python3 scratch/clash.py
new public short names checked (outside FlucVanishInst): 97; files scanned: 204 (main worktree RBM3D/ and this worktree RBM3D/, minus Green/FlucVanish.lean)
declaration clashes found: 0
```

### b.6 Statement diff against RBM2D `c9a24cf` (`python3 scratch/stmtdiff.py`: 3D signatures mapped back by the inverse of R1-R4, whitespace-normalised, compared as text)

```
RBM2D c9a24cf public declarations: 92  | RBM3D public declarations in FlucVanish.lean (outside FlucVanishInst): 97
textually equal after the inverse renaming (R1-R4): 83
  IsRowCoord decidableIsRowCoord isRowCoord_mk rowSplit rowSplit_apply_of_isRowCoord rowSplit_apply_of_not_isRowCoord rowSplit_rowSplit measurable_rowSplit preimage_rowSplit_pi measurePreserving_rowSplit condRow condRow_apply RowIntegrable measurable_rowSplit_right rowIntegrable_of_measurable_of_bound condRow_const condRow_condRow rowSplit_condRow condRow_sub condRow_sub_condRow FinDepOffRow FinDepOffRow.rowSplit_eq FinDepOffRow.comp condRow_of_finDepOffRow condRow_mul_of_finDepOffRow' integral_condRow finDepOffRow_of_minor greenMinorMat finDepOffRow_greenMinorMat finDepOffRow_greenMinorMat_apply greenMinorMat_eq_minorGreen crd GreenDeriv_crd_injective GreenDeriv_slice_apply Bmat GreenDeriv_Bmat_apply GreenDeriv_mem_usedCoords Xmat_eq_sum GreenDeriv_Bmat_isHermitian GreenDeriv_coordinateMatrix_eq_Bmat GreenDeriv_Xmat_update GreenDeriv_seqXmat_eq_sum GreenDeriv_seqXmat_update GreenDeriv_seqHflow_eq_realSmul GreenDeriv_continuous_seqHflow GreenDeriv_seqHflow_congr_of_agree finDep_of_Hflow hermCLM GreenDeriv_hermCLM_apply GreenDeriv_isHermitian_hermCLM GreenDeriv_hermCLM_of_isHermitian resH GreenDeriv_resH_eq_green GreenDeriv_resH_of_isHermitian GreenDeriv_isUnit_resH_arg hasFDerivAt_resH continuous_green_comp sub_smul_one_apply finDepOffRow_const FinDepOffRow.mul FinDepOffRow.sub finDepOffRow_prod finDepOffRow_condRow integrable_P_of_measurable_of_bound integral_mul_prod_eq_zero greenDiagCentered flucDiag greenMinorDiagCentered flucDiagMinor norm_flucDiag_sub_flucDiagMinor_le norm_sub_condRow_le norm_flucDiag_le norm_flucDiagMinor_le UniformWeight epsHom epsHom_inl epsHom_inr norm_epsHom epsHom_ofReal measurable_epsHom prod_epsHom prod_epsHom_sum_eq flucAvg
residual differences: 6
2D FlucVanish:374  theorem flucVanish_card_filter_sub_mem_sbSupport (a : Z2 L) : ((univ : Finset (Z2 L)).filter fun b => a - b ∈ sbSupport L).card = (sbSupport L).card
3D                  theorem flucVanish_card_filter_sub_mem_sbSupport (a : Zd d L) : ((univ : Finset (Zd d L)).filter fun b => b - a ∈ flucVanish_sbSupport d L).card = (flucVanish_sbSupport d L).card
2D FlucVanish:398  theorem flucVanish_card_svarSupport (i : Idx L W) : ((univ : Finset (Idx L W)).filter fun j => (blk L W i.1, blk L W i.2) - (blk L W j.1, blk L W j.2) ∈ sbSupport L).card = (sbSupport L).card * W ^ 2
3D                  theorem flucVanish_card_svarSupport (i : Idx d L W) : ((univ : Finset (Idx d L W)).filter fun j => (split d L W j).1 - (split d L W i).1 ∈ flucVanish_sbSupport d L).card = (flucVanish_sbSupport d L).card * W ^ d
2D FlucVanish:412  theorem flucVanish_card_svarSupport_eq (hL : 3 ≤ L) (i : Idx L W) : ((univ : Finset (Idx L W)).filter fun j => (blk L W i.1, blk L W i.2) - (blk L W j.1, blk L W j.2) ∈ sbSupport L).card = 5 * W ^ 2
3D                  theorem flucVanish_card_svarSupport_eq (hL : 3 ≤ L) (i : Idx d L W) : ((univ : Finset (Idx d L W)).filter fun j => (split d L W j).1 - (split d L W i).1 ∈ flucVanish_sbSupport d L).card = (2 * d + 1) * W ^ d
2D FlucVanish:419  theorem flucVanish_card_blockSupport (a : Z2 L) : ((univ : Finset (Idx L W)).filter fun k => (blk L W k.1, blk L W k.2) = a).card = W ^ 2
3D                  theorem flucVanish_card_blockSupport (a : Zd d L) : ((univ : Finset (Idx d L W)).filter fun k => (split d L W k).1 = a).card = W ^ d
2D FlucVanish:456  theorem uniformWeight_blockAvg2 (a : Z2 L) : UniformWeight (fun k : Idx L W => if (blk L W k.1, blk L W k.2) = a then (W : ℝ)⁻¹ ^ 2 else 0) ((W : ℝ)⁻¹ ^ 2) ((univ : Finset (Idx L W)).filter fun k => (blk L W k.1, blk L W k.2) = a)
3D                  theorem uniformWeight_blockAvg2 (a : Zd d L) : UniformWeight (fun k : Idx d L W => if (split d L W k).1 = a then ((W : ℝ) ^ d)⁻¹ else 0) (((W : ℝ) ^ d)⁻¹) ((univ : Finset (Idx d L W)).filter fun k => (split d L W k).1 = a)
2D FlucVanish:472  theorem flucVanish_blockAvg2_eq_blkCoef2 (a : Z2 L) (k : Idx L W) : (if (blk L W k.1, blk L W k.2) = a then (W : ℝ)⁻¹ ^ 2 else 0) = blkCoef2 L W a (splitEquiv L W k)
3D                  theorem flucVanish_blockAvg2_eq_blkCoef2 (a : Zd d L) (k : Idx d L W) : (if (split d L W k).1 = a then ((W : ℝ) ^ d)⁻¹ else 0) = blkCoef2 d L W a (splitEquiv d L W k)
in RBM2D, not in this file: 3: flucVanish_card_filter_blk2_mem flucVanish_card_sbSupport_le uniformWeight_svar
in this file, not in RBM2D: 8: BoundedWeight UniformWeight.toBoundedWeight flucVanish_card_filter_blk_mem flucVanish_sbSupport flucVanish_mem_sbSupport flucVanish_card_sbSupport boundedWeight_svarF not_uniformWeight_svarF
RBM2D c9a24cf lines of the key targets: CondRow:358 greenMinorMat_eq_minorGreen, GreenDeriv:354 continuous_green_comp, FlucVanish:472 flucVanish_blockAvg2_eq_blkCoef2
```

### b.7 Ports: commits, line citations, `d = 2` tokens

```
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h; rev-parse --short c9a24cf; diff --stat c9a24cf HEAD -- RBM2D/Green/{CondRow,GreenDeriv,FlucVanish}.lean | tail -1   # HEAD later than c9a24cf: RBM2D deleted dead code (kept lines 373/356/477)
9e0f275
c9a24cf
 3 files changed, 39 insertions(+), 317 deletions(-)
$ python3 scratch/tokens.py
token (comments and RBM2D private Checks removed)    RBM2D    RBM3D
W ^ 2                                                 4        0
(W⁻¹) ^ 2 / W⁻¹ ^ 2                                   7        0
Z2                                                    8        0
sbSupport L / 5-point                                22        0
blk L W k.1, blk L W k.2 (pair of blocks)            16        0
Fin W × Fin W                                         1        0
Sizes (2D `d : Sizes`)                              185        0
`W ^ d` / `(W:ℝ)^d)⁻¹`                                0        6
```

### b.8 Narrative

1. Delivered (b.1): `RBM3D/Green/FlucVanish.lean` (1613 lines) on `t/T2061`, commit 00aa135, plus one structural registry line in `RBM3D/Test/Axioms.lean` (inserted after the `FinDep` line). Imports: the four ticket modules, `Gauss/FlowCalculus` (S1-01, for `continuous_green_of_isHermitian`) and `Hierarchy/ContractionBasic` (S1-03, for `usedCoords`), the two dependencies S1-01 (T2030) and S1-03 (T2032) of the ticket header: the transitive closure grows by exactly these two modules (b.1); `RBM3D` itself is not imported.
2. Port (b.6): all 92 public declarations of CondRow (31, lines 65-358), GreenDeriv (26, 45-354), FlucVanish (35, 50-472) of `c9a24cf`; 83 statements are textually equal after the inverse of R1-R4, 6 differ, all FlucVanish block/support counts: `Z2 L` to `Zd d L`; the block pair `(blk L W k.1, blk L W k.2)` to `(split d L W k).1`; `W ^ 2` to `W ^ d`; `W⁻¹ ^ 2` to `((W:ℝ)^d)⁻¹`; `sbSupport L` to `flucVanish_sbSupport d L` (`{0} ∪ {|x|₁ = 1}`, `2d+1` points for `3 ≤ L`, `flucVanish_card_sbSupport`); `5` to `2d+1`; the row support is oriented `b_j - b_i` (DECISIONS §30), RBM2D has `a - b`.
3. Not ported (b.6). `uniformWeight_svar` (:428) is false at `d ≥ 3` for `g² ≠ 1`: compiled as `not_uniformWeight_svarF` and its instance at `g = 1/64`; replaced by `BoundedWeight`, `UniformWeight.toBoundedWeight`, `boundedWeight_svarF` (Amend 1; RBM2D users: FlucAvgDet:474, :590, FlucIter:1634). `flucVanish_card_sbSupport_le` (:388) has no RBM2D use outside this file except `uniformWeight_svar` (`git grep` at c9a24cf): replaced by `flucVanish_card_sbSupport`. `flucVanish_card_filter_blk2_mem` (:350, no use outside this file) is renamed `flucVanish_card_filter_blk_mem`. `flucVanish_card_svarSupport_eq`, `flucVanish_card_blockSupport` keep their names (used at FlucAvg:370, :360).
4. `BoundedWeight` has the five fields of (a) round 2. `Σ t = 1` for the row is proved (`flucVanish_sum_svarF_row`, a private copy of the private `RowIndep.sum_svarF_row`) but the structure records `Σ t ≤ 1`, which replaces `UniformWeight.mass` (`c · #A ≤ 1`, used at FlucIter:1017; for the row `c · #A = 2d + 1`). The other RBM2D uses are `hw.not_mem` (FlucIter:991), `hw.mem` (`t = c`, :996: needs `≤ c` downstream, DECISIONS §30) and `hw.nonneg`.
5. `d = 2` tokens (b.7): `W^2`, `W⁻¹^2`, `Z2`, `sbSupport`/`5`, block pairs, `Fin W × Fin W` and every `d : Sizes` token are absent from the code. CondRow has no exponent token (portmap); the `Z2` tokens of GreenDeriv were in a docstring and the Checks; the FlucVanish rows are those of (a) (i).
6. Instances (b.4): the three key targets and `boundedWeight_svarF` are applied at `sz0` with every deterministic hypothesis proved, at every sample `ω` (for `greenMinorMat_eq_minorGreen`: `IsUnit det` and `G_kk ≠ 0` hold for Hermitian `H` off the real axis; the Ward identity is a private port of RBM2D `LDE.lean:35-100`); the block count `32768 = W^d` and the support count `229376 = (2d+1) W^d` are proved at `sz0` (`flucVanish_blockAvg2_nondegenerate_sz0`, `boundedWeight_svarF_card_sz0`). No external hypothesis.
7. Lemmas whose statement names `IsRowCoord` at concrete sizes (`condRow_sub_condRow`, `integral_condRow`, the vanishing lemma, `X0_not_finDepOffRow`) are applied at `szS` (d = 3, L = 3, W = 1, 27 sites), not at `sz0`: stating `IsRowCoord sz0 0 k c` fails with `maximum recursion depth` (b.4 reproduction: `whnf` unfolds `IsRowCoord` to a membership in the explicit finite set `rowSet`); the same statement at L = 3, W = 1 elaborates.
8. Registry: `RBM.Green.IsRowCoord` was the only unclassified premise (the pre-check printed it before the line was added); registered as structural (a membership predicate that defines `E_k`, hypothesis of `rowSplit_apply_of_isRowCoord`). After the line the pre-check exits 0 (b.1).
9. Private helpers: `flucVanish_sum_svarF_row`, `flucVanish_sbKernelR_le_one`, `flucVanish_isUnit_det`, `flucVanish_im_green_diag`, `flucVanish_green_diag_ne_zero`. One linter warning: `prod_epsHom_sum_eq` keeps the `[DecidableEq κ]` of the RBM2D statement.

## (c) Verified Mathlib names (each compiled in `FlucVanish.lean`; line of the first use from `grep -nF`; no separate `#check`)

`Finset.card_insert_of_notMem` (1082), `ite_eq_right` (109), `ite_eq_left` (104), `Finset.sum_subset` (415), `Finset.card_image_of_injective` (1099), `Finset.single_le_sum` (1159), `Fintype.sum_equiv` (1142), `Matrix.nonsing_inv_eq_ringInverse` (640), `hasFDerivAt_ringInverse` (668), `Measure.eq_infinitePi` (156), `Measure.infinitePi_pi` (160), `Finset.prod_filter_mul_prod_filter_not` (163), `integral_integral` (302), `integral_map` (297), `integrable_map_measure` (295), `norm_integral_le_of_norm_le_const` (865), `Finset.prod_univ_sum` (1018), `Fintype.piFinset_univ` (1020), `Integrable.mono'` (190), `dotProduct_star_self_pos_iff` (1326), `im_star_dotProduct_mulVec_self` (1303), `dotProduct_single_one` (1301), `Matrix.isUnit_iff_isUnit_det` (1284), `LinearMap.toContinuousLinearMap` (603), `Complex.norm_exp_ofReal_mul_I` (1410), `Complex.exp_pi_div_two_mul_I` (1428), `Measurable.cexp` (1406), `Complex.measurable_ofReal` (1407)
Deprecated, avoided: `if_neg` (compiler warning, replaced by `ite_eq_right`). Names verified absent: none searched.

## (d) Open issues and paper-delta candidates

- T2061a (DECISIONS §30): the fluctuation-average row weight `j ↦ S_{ij}` is stated in Lean as `BoundedWeight` (`0 ≤ t ≤ W^{-d}` on the `(2d+1) W^d` sites of the block of `i` and its `2d` neighbours, `t = 0` elsewhere, `Σ t ≤ 1`), not as RBM2D's `UniformWeight` (`t = c` on the support), which is false at `d ≥ 3` for `g² ≠ 1` (`not_uniformWeight_svarF`). The paper states no such lemma; the block average `W^{-d} 1(k ∈ 𝓘_a)` stays a `UniformWeight`.
- Downstream (S1-18, S1-20, S1-30, DECISIONS §30; not done here): the hypothesis `UniformWeight (svar i ·) c A` becomes `BoundedWeight`, `hw.mass` becomes `hw.sum_le`, and `t = c` (FlucIter:996) is read as `t ≤ c`.
- Downstream instances that state `IsRowCoord` (or objects unfolding to it) at `sz0` fail to elaborate (b.4); use small sizes or a variable `sz`.
- `RowIndep.sum_svarF_row` is private (a private copy is in this file); making it public needs the dispatcher (file scope).
- Hub at merge: add `import RBM3D.Green.FlucVanish` after the last import line of `RBM3D.lean`. No external hypothesis, no owed premise, no `sorry`/`axiom`/`native_decide` (b.1, b.2).
