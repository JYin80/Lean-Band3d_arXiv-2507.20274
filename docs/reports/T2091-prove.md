Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 00:43:06 UTC 2026

Targets: port of RBM2D `Green/IBP.lean` at `c9a24cf` (git show: 1653 lines) to `d`-dimensions; key statement `ibpRem_eq_add` (IBP:1311).
Mathematics of the key statement (renamed `spectralM E`, `spectralZ E t`, `svar`, `d : Sizes` as `mE E`, `zt E t`, `svarF d L W (sz.lam n)`, `sz : Sizes d`; `m = mE E`, `G_u = green (seqHflow sz n u ω) (zt E t)`):

  `ibpRem(i,k)(ω) := E_i[G_ii (G_kk - m)] - m (G_kk - m)(ω)`
  `ibpRem(i,k)(ω) = E_i[(G_ii - m)(G_kk - m)] + m (E_i(G_kk - m) - (G_kk - m)(ω))`.

Proof of the key statement: `G_ii (G_kk-m) = (G_ii-m)(G_kk-m) + m(G_kk-m)` pointwise, linearity of `E_i = condRow` on tame functions, `E_i[m·f] = m·E_i f`. It uses no variance profile, no `d`, no Stein identity; hypotheses `hG`, `|E| < 2`, `t < 1` serve only tameness/integrability of `G`-entries (`‖G_ab‖ ≤ η_t⁻¹`, `η_t = (1-t) Im m`).

### (i) Exponent table

| # | Quantity | Value in the instance | Constraint | Slack |
|---|---|---|---|---|
| 1 | `E` | 1/2 | `|E| < 2` (`Im m > 0`; `ibpRem_eq_add`, `tame_*`) | 3/2 |
| 2 | `t` | 1/2 | `t < 1` (`Im z_t = (1-t) Im m > 0`); `0 ≤ t` only in the display `condExpDiag_eq_sum_Sblk` and `condRow_Hflow_mul_green_diag` | 1/2 |
| 3 | `η_t = (1-t) Im m` | 0.4841229 | `‖G_ab‖ ≤ η_t⁻¹ = 2.0656` (tameness) | observed `max_j |G_jj|` = 1.4156 (script) |
| 4 | `L` | 3 | `3 ≤ L` (`sz.three_le_L n`): `card_nbhd` (`Defs/Neighbours.lean:158`, needs `3 ≤ L`) gives the `2d` neighbours in the row sum | 0 (tight, holds for every `Sizes d`) |
| 5 | `W` | 2 | `0 < W` | 1 |
| 6 | `g = sz.lam n` | 1/2 | no constraint (`svarF ≥ 0` for every real `g`, `a = (1+2dg²)⁻¹ > 0`) | none needed |
| 7 | `d` | 3 | `Sizes d` carries no `3 ≤ d`; no target needs it | `d` free |
| 8 | `N = (WL)^d = sz.size n` | 216 | matrix dimension, `card (Idx d L W)` | - |
| 9 | `S_ii = W^{-d}(1+2dg²)⁻¹` | 1/8 · 0.4 = 0.05 (RBM2D: `1/5` fixed profile) | `gvarF = S_ii` on the diagonal, `S_ij/2` off it | - |
| 10 | neighbour-block `S_ij = g² a/W^d` | 0.0125 per site | `≥ 0` | - |
| 11 | row sum `Σ_k svarF i k` | `8·0.05 + 6·8·0.0125 = 0.4 + 0.6 = 1` | `= 1` for `3 ≤ L`: `W^{-d}·W^d·(a + 2d g² a)`; RBM2D `IBP_sum_svar_row` (`5` points, `(5W²)⁻¹`) | 0 (identity) |
| 12 | row support `{k : svarF i k > 0}` | `(2d+1) W^d = 56` fine sites (RBM2D `5 W²`); not used by this file | - | - |
| 13 | per-site cap `svarF ≤ c` | `c = W^{-d}` (RBM2D `(5W²)⁻¹`, uniform) | not used by this file; only comment at IBP:53 | - |

Statement-by-statement `d`-dependence (all public declarations of RBM2D `Green/IBP.lean`, lines 1-1346 of the git-show text):
- Dimension-free after renaming R1/R2/R4 (no exponent, no profile value): `hasDerivAt_Hflow_update` (113), `hasDerivAt_green_Hflow_update` (133), `tame_green_apply` (268), `hasDerivAt_green_apply_update` (304), `tame_green_mul_mul_green_apply` (333), `integral_coord_mul_green_apply` (356), `sum_gvar_Bmat_sandwich_diag(_mul)` (661, 671; generic symmetric nonnegative profile, `gvar = svar` diagonal, `svar/2` off it, which is `gvarF` by definition), `tame_const_mul_green_apply`, `tame_const_mul_sandwich_apply`, `integral_coord_mul_Bmat_mul_green_diag` (706-737), `condRow_coord_mul`, `condRow_const_mul`, `condRow_neg_const_mul`, `condRow_finsetSum`, `condRow_zero_apply` (866-915), `Bmat_mul_apply_diag_of_ne` (923), `hasDerivAt_const_mul_green_apply_update` (935), `condRow_coord_mul_Bmat_mul_green_diag` (980), `condRow_Hflow_mul_green_diag` (1023; value `-u Σ_k S_ik E_i[G_ii G_kk]` with `S = svarF`), `tame_Hflow_mul_green_apply`, `condRow_tame_add`, `condRow_tame_sub` (1144-1169), `ibpRem` (1298), `ibpRem_eq_add` (1311).
- One statement whose proof changes: `IBP_sum_svar_row` (1180), `Σ_k svar L W i k = 1`. RBM2D proof: `svar_cast_eq_Spaper` and `RBM.sum_Spaper_row`. In `d` dimensions: `Σ_k svarF d L W g i k = 1` for `3 ≤ L`, via the fibre of `split` (`W^d` points per block, `W^{-d}·W^d = 1`) and `Σ_b SB d L g a b = 1` (`sum_SB_row`, `Defs/Block.lean:108`, row sum `a + 2d g² a = 1`). Statement unchanged apart from renaming (`svar L W` to `svarF d L W g`, `Idx L W` to `Idx d L W`).
- `condExpDiag_eq_sum_Sblk` (1194): same shape with `svarF d (sz.L n) (sz.W n) (sz.lam n)`; the display `E_i(G_ii-m) = t m Σ_k S_ik E_i[G_ii(G_kk-m)]` is checked by script at the instance (below).
- Stein hypothesis: `hG : GaussIBP d` becomes `GaussIBP sz`, discharged by `gaussIBP sz` (unconditional, no further hypothesis; `Sizes d` needs only `3 ≤ L`, `0 < W`).
- `UniformWeight`/`BoundedWeight` (DECISIONS §30): grep of the RBM2D file for `UniformWeight`, `BoundedWeight`, `scaleM`, `ellT`, `ellStar`, `tailT`, `Meta`, `ellz` returns no match, so the §30 replacement does not enter this file.
- `d = 2` tokens of portmap row 44 (`d=2:2`, `Z2/zdist2:1`, `1/5:2`) are at IBP lines 50, 51, 53 (module docstring: `d = 2`, `Z2 (W L)`, `(5 W²)⁻¹`), 1522 (`d = 2` in the `Checks` docstring), 1351, 1607, 1618-1619 (`Checks` section: `1/5`, nine and thirty-six sites). None is in a declaration signature or a proof of the kept lines; the single `d`-dependent proof is the row sum above. Replaced in docstrings; instance data replaced by the `d = 3` instance below.

### (ii) One concrete nondegenerate instance

Instance: `d = 3`, `L = 3`, `W = 2`, `g = 1/2` (constant `Sizes 3`: `L n = 3`, `W n = 2`, `lam n = 1/2`; admissible since `Sizes d` requires only `3 ≤ L`, `0 < W`), `n` arbitrary, `E = 1/2`, `t = 1/2`, one sample `ω` (`X0`, seed 12345), `i = x(0,0,0)`, `k ∈ {i, (2,0,0), (1,1,0)}`. All hypotheses of `ibpRem_eq_add` hold: `GaussIBP` is the theorem `gaussIBP sz`; `|E| = 1/2 < 2`; `t = 1/2 < 1`; `i`, `k`, `ω` arbitrary. Matrix dimension `N = 216`; the 216-point lattice `Z_6^3`, blocks `Z_3^3`, fibre `W^d = 8`, `E_i` integrates the `N` complex row-`i` entries (real diagonal `S_ii`, complex off-diagonal of variance `S_ij`, i.e. `gvarF = S_ij/2` per real coordinate), approximated by `M = 20000` fresh rows; the two sides of `ibpRem_eq_add` are linear in the same empirical measure, so they agree to rounding for every `M` (a check of the algebra with the `d = 3` data, not of the Gaussian law). The display is a genuine Gaussian identity; it is checked statistically (paired, standard error).

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2091/ibp_check.py` (numpy 2.0.2; 32 s). Output:

```
N = 216 row sums min/max: 1.0 1.0 S_ii = 0.05 expected 0.05
eta_t = (1-t) Im m = 0.4841229182759271 ; 1/eta_t = 2.065591117977289 ; max_s max_j |G_jj| over samples below checked afterwards
m = (-0.25+0.9682458365518543j) z_t = (0.375+0.4841229182759271j) |m(m+E)+1| = 0.0
--- ibpRem_eq_add: both sides, empirical E_i over M = 20000 fresh rows (linear functional) ---
i=0 k=  0 S_ik=0.050000  LHS=-0.122429911447+0.277222631612j RHS=-0.122429911447+0.277222631612j |LHS-RHS|=2.78e-17
i=0 k= 72 S_ik=0.012500  LHS=0.000669211096+0.000393241469j RHS=0.000669211096+0.000393241469j |LHS-RHS|=1.08e-18
i=0 k= 42 S_ik=0.050000  LHS=0.003252217684+0.001933009722j RHS=0.003252217684+0.001933009722j |LHS-RHS|=9.95e-18
--- display  E_i(G_ii-m) = t m sum_k S_ik E_i[G_ii(G_kk-m)]  (Monte Carlo, paired) ---
mean D = -5.502e-04+2.918e-06j, SE = 1.362e-03, |mean D|/SE = 0.40 ;  |E_i(G_ii-m)| = 1.039e-02
E_i(G_ii-m) = -0.008364+0.006157j ; RHS = -0.007814+0.006154j
sensitivity (uniform weight 1/((2d+1)W^d) on the support instead of svarF): |mean D|/SE = 5.67
max |G_jj| over 20000 samples, all j: 1.4156 <= 1/eta_t = 2.0656
```

(The first output line printed `S_ii` and the row sums: `svarF` rows sum to 1 at `d = 3`, `L = 3`, `W = 2`, `g = 1/2`, with `S_ii = W^{-d}(1+2dg²)⁻¹ = 0.05`. The line with `checked afterwards` refers to the last output line.) External hypotheses: none (`gaussIBP sz` is a merged theorem), so no limit computation is required.

### Verdicts

- `ibpRem_eq_add` (and `ibpRem`): **PASS**. Hypotheses hold at the instance; statement true at `d = 3` after renaming; no exponent changes; both sides agree (`|LHS-RHS| ≤ 2.8e-17`).
- Remaining declarations of the file (ported, list above): **PASS**. No statement is false at `d ≥ 3`; the only `d`-dependent step is the row sum `Σ_k svarF i k = 1` (row 11), verified at the instance and implied by `sum_SB_row` plus the fibre count `W^d`; the display `condExpDiag_eq_sum_Sblk` is consistent at `d = 3` (`|mean D|/SE = 0.40`; the uniform-weight alternative is rejected at 5.67 SE).
- Nothing in the file is dropped by this preflight.

## (a′) Preflight corrections — Sun Oct  4 01:10:32 UTC 2026

Two points of (a), neither changes a verdict (script: `grep -n "hu : 0 ≤ u\|ht0 : 0 ≤ t\|card_nbhd\|sum_sbKernelR" RBM3D/Green/IBP.lean`):
- Row 2: the hypothesis `0 ≤ u` (flow time) is that of `condRow_Hflow_mul_green_diag` (IBP.lean:1044); `0 ≤ t` is that of `condExpDiag_eq_sum_Sblk` (IBP.lean:1228), which applies it at `u = t`.
- Rows 4, 11: the Lean proof of `Σ_k svarF i k = 1` uses `sum_sbKernelR` (`Defs/Block.lean:93`, needs `3 ≤ L`) and the `W^d` fibre of `split` (IBP.lean:1203, 1211), not `card_nbhd`; the constraint `3 ≤ L` and its slack 0 are unchanged.

## (b) Script output — Sun Oct  4 01:10:32 UTC 2026

Prover `claude-sonnet-5-5`, role `prover-hard`.  Branch `t/T2091`.  Sole writable file `RBM3D/Green/IBP.lean` (new); `RBM3D/Test/Axioms.lean` unchanged (narrative 5).

```
$ git log -1 --format="%h %an <%ae> %cd" --date=iso-strict; git diff --name-only main...t/T2091; wc -l RBM3D/Green/IBP.lean
e667488 Jun Yin <321276894+JYin80@users.noreply.github.com> 2026-10-03T18:07:31-07:00
RBM3D/Green/IBP.lean
    1687 RBM3D/Green/IBP.lean
$ lake env lean RBM3D/Green/IBP.lean   (fresh compile of the committed file)
exit=0, no output (no warning, no error)
$ lake build RBM3D.Green.IBP 2>&1 | tail -1
Build completed successfully (3335 jobs).
$ lake build 2>&1 | tail -2   (full library with root #assert_rbm_axioms; the root does not import the new module yet)
non-vacuity certificates: 4 of 97 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (3833 jobs).
$ grep -nE "sorry|admit|native_decide|\baxiom\b" RBM3D/Green/IBP.lean   ->  exit=1 (no match)
```
```
$ lake env lean precheck/Axioms.lean   (27 lines "#print axioms RBM.Green.<name>", one per public declaration; scratch outside the repository)
'RBM.Green.ibpRem_eq_add' depends on axioms: [propext, Classical.choice, Quot.sound]
$ sed "s/.*axioms: //" axioms.txt | sort | uniq -c   ->   27 [propext, Classical.choice, Quot.sound]
```
```
$ extract.py ibpRem_eq_add condExpDiag_eq_sum_Sblk IBP_sum_svarF_row   (text of each declaration up to its first ":=", from RBM3D/Green/IBP.lean)
-- IBP.lean:1344
theorem ibpRem_eq_add (hE : |E| < 2) (ht : t < 1)
    (i k : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    ibpRem sz n E t (i, k) ω
      = condRow sz n i (fun η => (green (Sizes.seqHflow sz n t η) (zt E t) i i
            - mE E)
          * (green (Sizes.seqHflow sz n t η) (zt E t) k k - mE E)) ω
        + mE E * (condRow sz n i
            (greenDiagCentered sz n t (zt E t) (mE E) k) ω
          - (green (Sizes.seqHflow sz n t ω) (zt E t) k k - mE E))
-- IBP.lean:1227
theorem condExpDiag_eq_sum_Sblk (hE : |E| < 2) (hE2 : |E| ≤ 2)
    (ht0 : 0 ≤ t) (ht : t < 1) (i : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    condExpDiag sz n t (zt E t) (mE E) i ω
      = (t : ℂ) * mE E * ∑ k, (svarF d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ)
          * condRow sz n i (fun η => green (Sizes.seqHflow sz n t η) (zt E t) i i
              * (green (Sizes.seqHflow sz n t η) (zt E t) k k - mE E)) ω
-- IBP.lean:1205
theorem IBP_sum_svarF_row {L W : ℕ} [NeZero L] [NeZero W] (g : ℝ) (hL : 3 ≤ L)
    (i : Idx d L W) : ∑ k : Idx d L W, svarF d L W g i k = 1
$ grep -n -A4 "^noncomputable def ibpRem" RBM3D/Green/IBP.lean
1331:noncomputable def ibpRem (sz : Sizes d) (n : ℕ) (E t : ℝ)
1332-    (q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) : ℂ :=
1333-  condRow sz n q.1 (fun η => green (Sizes.seqHflow sz n t η) (zt E t) q.1 q.1
1334-      * (green (Sizes.seqHflow sz n t η) (zt E t) q.2 q.2 - mE E)) ω
1335-    - mE E * (green (Sizes.seqHflow sz n t ω) (zt E t) q.2 q.2 - mE E)
```
```
$ python3 stmtdiff.py   (the 27 public declarations of RBM2D Green/IBP.lean lines 1-1346 at c9a24cf, statement text up to ":=", renamed by R1-R4 + R5 (drop (hG : GaussIBP sz)) vs the same declaration here)
public declarations in RBM2D lines 1-1346: 27  identical after renaming rules: 26  differing: 1
===== IBP_sum_svar_row
--- RBM2D(renamed)
+++ RBM3D
@@ -1 +1,2 @@
-theorem IBP_sum_svarF_row {L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L)
+theorem IBP_sum_svarF_row {L W : ℕ} [NeZero L] [NeZero W] (g : ℝ)
+(hL : 3 ≤ L)
```
```
$ sed -n "1396,1407p;1595,1606p;1618,1623p;1658,1662p;1670,1672p" RBM3D/Green/IBP.lean   (in `section Checks`: data; the display; key target at (x0,x1), (x0,x0); nondegeneracy)
private def ckS : Sizes 3 where
  L := fun _ => 3
  W := fun _ => 2
  lam := fun _ => 1 / 2
  three_le_L := fun _ => le_rfl
  W_pos := fun _ => by norm_num
private abbrev ckI : Type := Idx 3 (ckS.L 0) (ckS.W 0)
private def ckx0 : ckI := fun _ => 0
private def ckx1 : ckI := Pi.single 0 1
private def ckx2 : ckI := Pi.single 1 1
/-- **T-G**: `condExpDiag_eq_sum_Sblk` at `d = 3`, `L = 3`, `W = 2`, `lam = 1/2`,
`E = t = 1/2`, `i = x0`, for every `ω`. -/
example (ω : Sizes.SeqΩ ckS) :
    condExpDiag ckS 0 (1 / 2) (zt (1 / 2) (1 / 2)) (mE (1 / 2)) ckx0 ω
      = ((1 / 2 : ℝ) : ℂ) * mE (1 / 2) * ∑ k : ckI, (svarF 3 3 2 (1 / 2) ckx0 k : ℂ)
          * condRow ckS 0 ckx0 (fun η =>
              green (Sizes.seqHflow ckS 0 (1 / 2) η) (zt (1 / 2) (1 / 2)) ckx0 ckx0
              * (green (Sizes.seqHflow ckS 0 (1 / 2) η) (zt (1 / 2) (1 / 2)) k k
                - mE (1 / 2))) ω :=
  condExpDiag_eq_sum_Sblk (n := 0) (E := 1 / 2) (t := 1 / 2) (sz := ckS) ck_hE ck_hE2 ck_ht0
    ck_ht ckx0 ω
example (ω : Sizes.SeqΩ ckS) :=
  ibpRem_eq_add (n := 0) (E := 1 / 2) (t := 1 / 2) (sz := ckS) ck_hE ck_ht ckx0 ckx1 ω
example (ω : Sizes.SeqΩ ckS) :=
  ibpRem_eq_add (n := 0) (E := 1 / 2) (t := 1 / 2) (sz := ckS) ck_hE ck_ht ckx0 ckx0 ω
/-- **Nondegeneracy of the data**: the row sum `Σ_k svarF(i,k) = 1` at `L = 3`, `W = 2`,
`g = 1/2` (`IBP_sum_svarF_row`), the diagonal weight `svarF(i,i) = W^{-d}(1 + 2dg²)⁻¹ = 1/20`,
`216` sites, and a positive variance `gvarF = svarF_xx = 1/20` of the coordinate of the checks. -/
example : ∑ k : ckI, svarF 3 (ckS.L 0) (ckS.W 0) (ckS.lam 0) ckx0 k = 1 :=
  IBP_sum_svarF_row (ckS.lam 0) (ckS.three_le_L 0) ckx0
example : Fintype.card ckI = 216 := by
  rw [Sizes.card_Idx ckS 0]
  rfl
$ grep -c "^example" RBM3D/Green/IBP.lean   ->  38
$ occurrences of each of the 27 public names in the code of `section Checks` (comments stripped; all >= 1):
hasDerivAt_Hflow_update:2  hasDerivAt_green_Hflow_update:1  hasDerivAt_green_apply_update:1
hasDerivAt_const_mul_green_apply_update:1  tame_green_apply:6  tame_green_mul_mul_green_apply:1
tame_const_mul_green_apply:1  tame_const_mul_sandwich_apply:1  tame_Hflow_mul_green_apply:1
integral_coord_mul_green_apply:2  integral_coord_mul_Bmat_mul_green_diag:1  sum_gvar_Bmat_sandwich_diag:2
sum_gvar_Bmat_sandwich_diag_mul:1  condRow_coord_mul:1  condRow_const_mul:1  condRow_neg_const_mul:1
condRow_finsetSum:1  condRow_tame_add:1  condRow_tame_sub:1  condRow_zero_apply:1  Bmat_mul_apply_diag_of_ne:1
condRow_coord_mul_Bmat_mul_green_diag:3  condRow_Hflow_mul_green_diag:1  condExpDiag_eq_sum_Sblk:1  ibpRem:1
ibpRem_eq_add:2  IBP_sum_svarF_row:1
```
```
$ clash.sh names.txt   (27 new public names; per name a grep for a declaration with that name in RBM3D/**/*.lean of the main worktree)
names checked: 27, with a declaration in main: 0
$ same check for the 24 private names (clash.sh priv_names.txt)
names checked: 24, with a declaration in main: 0
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h c9a24cf ; git -C ../RBM2D --no-optional-locks log -1 --format=%h   (port source commit; RBM2D HEAD)
c9a24cf
9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Green/IBP.lean
 RBM2D/Green/IBP.lean | 592 ++++++++-------------------------------------------
 1 file changed, 84 insertions(+), 508 deletions(-)
$ git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Green/IBP.lean | wc -l
    1653
```
```
$ lake env lean precheck/Precheck.lean   (scratch outside the repository: import RBM3D; import RBM3D.Green.IBP; #assert_rbm_axioms)
axiom audit: 2973 theorems, 1137 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
14:  RBM.Green.GaussIBP: 23 [no certificate]
non-vacuity certificates: 4 of 97 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/Int
$ same file with only "import RBM3D" (baseline = main)
axiom audit: 2946 theorems, 1136 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
14:  RBM.Green.GaussIBP: 23 [no certificate]
```
```
$ git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Green/IBP.lean | grep -nE "d = 2|Z2|zdist2|1 ?/ ?5|5 W|W\^2|W²|UniformWeight|BoundedWeight|scaleM|ellT|ellStar|tailT|Meta|ellz" | cut -c1-100
50:* **d = 2 change (T2127 (b.4) rows 1, 13).**  RBM1D's `Sblk` becomes the variance profile `svar`
51:  on the fine index `Idx L W = Z2 (W L)` (DECISIONS §58).  The row sum `Σ_k svar(i,k) = 1`
53:  variance is `svar ≤ (5 W²)⁻¹`.  The block profile `Sblk2` enters only through the merged
1351:of them in each row of the profile, `svar = 1/5`), slice `n = 0`, `E = 1/2` (`|E| = 1/2 < 2`),
1522:/-- **T-G**: `condExpDiag_eq_sum_Sblk` (`d = 2` form, `svar` for `Sblk`) at `L = 3`, `W = 1`,
1606:/-- Nondegeneracy of the data: nine and thirty-six sites, five blocks of `W²` sites in each row
1607:the profile, and a positive variance `gvar = svar_{xx} = 1/5` of the coordinate of the checks. 
1618:example : (Sizes.seqGvar ckS (crd ckS 0 ckp0) : ℝ) = 1 / 5 := by
1619:  change (gvar 3 1 ((0, 0), (0, 0), true) : ℝ) = 1 / 5
$ grep -nE "<same pattern>" RBM3D/Green/IBP.lean | cut -c1-100   (this file; line 1384 matches "d = 216")
17:(item 2): `d : Sizes` becomes `sz : Sizes d`, `Z2 L`/`Idx L W` become `Zd d L`/`Idx d L W`,
57:  RBM2D (`UniformWeight`, DECISIONS §30) do not occur in this file.
1384:`n = 0` (`N = (W L)^d = 216` sites `Idx 3 3 2`, blocks of `W^d = 8` fine sites, diagonal varian
$ grep -nE "H_u \+ m|H_u\+m|H_u \+ t m|-m \(H|-m\(H" paper/tex/*.tex   (the 2D paper identity G_u - m = -m(H_u + m)G_u)
exit=1 (no match)
```
```
$ grep -rnE "ibpRem|condExpDiag_eq_sum_Sblk|IBP_sum_svar" RBM3D --include=*.lean   (main worktree: consumers of the new names)
exit=1 (no consumer)
$ git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Green/CondDom.lean | grep -nE "theorem norm_condExpDiag_sub_le_offdiag|condExpDiag_eq_sum_Sblk hG" | cut -c1-100
217:theorem norm_condExpDiag_sub_le_offdiag (hG : GaussIBP d) (hE : |E| < 2) (ht0 : 0 ≤ t)
241:    rw [condExpDiag_eq_sum_Sblk hG hE hE.le ht0 ht i ω,
$ git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Green/IBPRem.lean | grep -nE "ibpRem_eq_add \(gaussIBP d\)" | cut -c1-110
371:  rw [ibpRem_eq_add (gaussIBP d) (hE n) (ht1 n) v.1.1 v.1.2 ω]
487:  rw [ibpRem_eq_add (gaussIBP d) (hE n) (ht1 n) i i ω]
```

### Narrative

1. Port: all 27 public declarations of RBM2D `Green/IBP.lean:1-1346` (`c9a24cf`) are in `RBM3D/Green/IBP.lean` (1687 lines), none dropped; the 24 private helpers stay private. `IBP_gvar_eq` is now `IBP_gvarF_eq` and is `rfl` (`gvarF` is `svarF` or `svarF/2` by definition).
2. Rules of the statement diff: R1 `d : Sizes` to `sz : Sizes d` (`Sizes.SeqΩ d`, `Tame d`, `condRow d n`, `d.L n` to `sz.L n`); R2 `Idx L W`, `Bmat L W`, `usedCoords L W` to `... d L W`; R4 `Coord` to `CoordF`, `svar L W i k` to `svarF d (sz.L n) (sz.W n) (sz.lam n) i k`, `spectralM/Z` to `mE`/`zt`; R5 below. R3 (`W^2` to `W^d`) is not needed: no exponent occurs in a declaration.
3. Residual differences, 26 of 27 identical after R1-R5: `IBP_sum_svar_row` becomes `IBP_sum_svarF_row`, which takes the coupling `g` and has a new proof. It is the only `d`-dependent step: the fibre of `split` has `W^d` points, `W^{-d} W^d = 1`, and the block row sum is `sum_sbKernelR` (`3 ≤ L`).
4. R5 (ticket line 8): the ten statements that took `hG : GaussIBP` (`integral_coord_mul_green_apply`, `integral_coord_mul_Bmat_mul_green_diag`, `condRow_coord_mul`, `condRow_finsetSum`, `condRow_tame_add`, `condRow_tame_sub`, `condRow_coord_mul_Bmat_mul_green_diag`, `condRow_Hflow_mul_green_diag`, `condExpDiag_eq_sum_Sblk`, `ibpRem_eq_add`) do not take it; their proofs use the theorem `gaussIBP sz` (T2088). I dropped rather than kept it because no merged file or pin mentions these names (grep above), and because the pre-check shows `RBM.Green.GaussIBP` with 23 dependents on main and 23 with this file, so the file adds none to the owed ledger. A statement without the premise is stronger. RBM2D `CondDom:217,241` passes `hG`; that port (S1-24) drops the argument.
5. Registry: no line added (no new `Prop` predicate is taken as a hypothesis); the pre-check compiles with exit 0; `RBM3D/Test/Axioms.lean` is unchanged. The owed line `RBM.Green.GaussIBP` is untouched (the docstring of `Green/IBPPoly.lean` calls it superfluous now that `gaussIBP` exists; the cleanup ticket removes it).
6. Reused, not copied: `Tame`, `GaussIBP`, `polyW`, `condRow`, `rowSplit`, `IsRowCoord`, `Bmat`, `crd`, `hermCLM`, `resH`, `hasFDerivAt_resH`, `finDep_of_Hflow`, `continuous_green_comp`, `condExpDiag`, `norm_green_apply_le_etaT`, `mE_mul_add_zt`, `usedCoords`, `svarF`, `gvarF`. The file imports `Green/IBPPoly`, `Green/FlucVanish`, `Green/LDE`, never `RBM3D`. Copied as private: `Tame.comp_rowSplit`, `rowSplit_update`, `polyW_rowSplit_le`, `continuous_rowSplit_right`, `entryCLM`, `green_sub_smul_one_eq`, `zt_im_ne_zero_of_lt_one` and the sandwich/bookkeeping lemmas (no private or public name of the file exists in `RBM3D` main: name-clash greps above).
7. Instances: 38 `example`s in `section Checks` at `d = 3`, `L = 3`, `W = 2`, `lam = 1/2` (216 sites), `E = t = u = 1/2`; every public name is applied (counts above), `ibpRem_eq_add` at `(x0,x1)` and `(x0,x0)`. Nondegeneracy examples: row sum `1`, `svarF(x0,x0) = 1/20`, `216` sites, `gvarF = 1/20 > 0` at the diagonal coordinate. No hypothesis is left open. The Lean sites `(0,0,0)`, `(1,0,0)`, `(0,1,0)` differ from the preflight script sites.
8. `set_option maxRecDepth 100000` is scoped to `section Checks`: at the default depth applications with a hypothesis `p ∈ usedCoords 3 3 2` (e.g. `hasDerivAt_Hflow_update`) failed with "maximum recursion depth" (the profiler trace showed `whnf` unfolding the membership through the `Finset.univ` of `CoordF`, two copies of `Idx 3 3 2` (216 points) and `Bool`). `Green/FlucVanish.lean:1382-1388` avoids it with `W = 1` (27 sites).
9. The RBM2D negative check of the identity without the factor `t` (`G_u - m = -m(H_u + m)G_u`, false at `u = 0`, `E = 0`) is kept as a dimension-free example; its pattern does not occur in `paper/tex` (grep above), so no paper delta is claimed for it.
10. `d = 2` tokens (portmap row 44): the 9 RBM2D hits (lines 50, 51, 53, 1351, 1522, 1606, 1607, 1618, 1619) lie in the module docstring or in `Checks`, none in a declaration of lines 1-1346; they are replaced by the `d = 3` docstring and instances. The file has no `UniformWeight`/`BoundedWeight`/`ellT`-type token in code.

## (c) Verified names

Checked by `#check @name` in a scratch file importing `RBM3D.Green.IBP` (`lake env lean`, exit 0, no error); 99 Mathlib/core names used by the new code (the bare `integral_*` are `MeasureTheory.*` under `open MeasureTheory`; `ite_eq_left/right` are in `Init.Core`):
Bool.false_eq_true, Complex.I, Complex.I_sq, Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_sum, Complex.real_smul, Complex.real_smul.symm,
Complex.zero_im, Continuous.matrix_elem, ContinuousLinearMap.coe_comp, ContinuousLinearMap.mulLeftRight, ContinuousLinearMap.mulLeftRight_apply, Equiv.subLeft,
Filter.Eventually.of_forall, Finset.card_univ, Finset.mem_filter, Finset.mem_univ, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_comm, Finset.sum_congr,
Finset.sum_const, Finset.sum_eq_single, Finset.sum_eq_zero, Finset.sum_filter, Finset.sum_ite_eq', Finset.sum_le_sum, Finset.sum_mul, Finset.sum_neg_distrib,
Finset.sum_nonneg, Finset.sum_sub_distrib, Finset.univ, Finset.univ.filter, Fintype.card, Fintype.card_fin, Fintype.sum_bool, Fintype.sum_equiv,
Fintype.sum_prod_type, Function.Injective, Function.comp_apply, Function.comp_def, Function.update, Function.update_eq_self, Function.update_of_ne,
Function.update_self, HasDerivAt.const_mul, HasDerivAt.fun_sum, LinearMap.mkContinuous, Matrix.mul_apply, Matrix.neg_apply, Matrix.neg_mul, Matrix.of,
Matrix.one_apply_eq, Matrix.one_apply_ne, Matrix.one_mul, Matrix.smul_apply, Matrix.smul_mul, Matrix.sub_apply, Matrix.sub_mul, Matrix.sum_apply,
MeasureTheory.integral_finsetSum, Nat.cast_ne_zero, Nat.cast_pow, Pi.single, Pi.single_apply, Pi.single_eq_same, Real.mul_self_sqrt, Real.sqrt, add_smul, asymm,
hasDerivAt_id, integral_add, integral_const_mul, integral_neg, integral_sub, integral_zero, ite_eq_left, ite_eq_right, lt_irrefl, lt_trichotomy,
mul_inv_cancel₀, mul_le_mul_of_nonneg_left, mul_pos, mul_pow, mul_smul, neg_mul, neg_smul, neg_zero, one_smul, pow_le_pow_left₀, pow_ne_zero, smul_add,
smul_neg, smul_smul, smul_sub, sub_eq_self, two_smul, zero_sub
Verified absent from RBM3D (`#check` gives "Unknown identifier/constant", `Absent.lean`): `RBM.Ind.norm_apply_le_l2_opNorm`, `RBM.sum_Spaper_row`, `RBM.Green.svar_cast_eq_Spaper`, `RBM.Gauss.Sizes.constantSizes`, `RBM.Gauss.Sizes.seqHflow_zero`, `RBM.Gauss.gvar_diag`, `RBM.Gauss.gvar_offDiag`, `RBM.spectralM`, `RBM.Gauss.spectralM`, `RBM.Gauss.spectralZ`, `RBM.Green.spectralM`, `spectralM_quadratic`.

## (d) Open issues and paper-delta candidates

- `T2091a`: `Green/IBP.lean` is not a numbered statement of the paper: `paper/tex/3_5_Loop_Hierarchy.tex:37` leaves the proof of `(GavLGEX)` (`3_5:33`) to `[YY_25]` Lemma 4.1 as "dimension-independent"; the file proves the exact display `condExpDiag_eq_sum_Sblk` and the splitting `ibpRem_eq_add` with explicit remainder `ibpRem`.
- Signed entries cited, not re-proposed: D1 (`3 ≤ L`, used by `IBP_sum_svarF_row`); D129-D130 (profile, from the ticket text); D157 (`GaussIBP` proved).
- S1-24 and S1-29 ports: RBM2D `CondDom:217,241` and `IBPRem:371,487` pass `(gaussIBP d)` / `hG` to `condExpDiag_eq_sum_Sblk` and `ibpRem_eq_add`; here these take no such argument. If the dispatcher wants the hypothesis kept, one wrapper per statement restores it; not done.
