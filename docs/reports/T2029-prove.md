Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 05:24:58 UTC 2026

Sources: `../RBM2D` at `c9a24cf`, `RBM2D/Green/Minor.lean` (317 lines; Check section from line 273 not ported) and `RBM2D/Green/EntryCore.lean` (1014 lines; Check section from line 846 not ported). Both files state that they are finite algebra over an arbitrary `[Fintype n] [DecidableEq n]` index type with no lattice, block or dimension.

### (i) Exponent table (key statements, dimension role, constants)

| Statement (file:line @c9a24cf) | Says | Dimension role | Constraint / constant | Slack at instance (delta=1/8, Phi=1) |
|---|---|---|---|---|
| Minor:255 `green_diag_paper` | (4.7): `G_ii = (H_ii - z - sum_{k,l!=i} H_ik G^(i)_kl H_li)^-1`, needs `IsUnit det(H-z)`, `G_ii != 0` | none (index type `n` arbitrary; `n := Zd d L` or a block-site type is only instantiated downstream) | none | residual 9.0e-16 (script) |
| Minor:242 `green_off_diag_paper` | (4.8): `G_ij = -G_ii sum_{k!=i} H_ik G^(i)_kj` (sign minus, as in RBM2D) | none | none | residual 1.5e-16 |
| Minor:233 `inv_minor_resolvent` | (4.9): `(H^(i)-z)^-1 = G_jk - G_ji G_ik/G_ii` | none | none | residual 2.4e-15 |
| EntryCore:175 `GoodEvent` + `norm_diag_le`, `one_sub_le_norm_diag`, `half_le_norm_diag`, `norm_sq_diag_le`, `norm_greenMinor_sub_le` | `max_xy |G_xy - m 1_{x=y}| <= delta`; with `|m|=1`: `1-delta <= |G_xx| <= 1+delta`, `|G_xx|^2 <= 9/4`, `|G^(i)_kl - G_kl| <= 2 |G_ki||G_il|` | `delta` is an abstract real (paper `delta = W^{-c}`: appears only in a docstring, not in any statement) | `delta <= 1/2` | delta<=1/2: slack 0.375; `1-delta`=0.875>=1/2; `(1+delta)^2`=1.2656<=9/4 |
| EntryCore `absorb_le`, `norm_sq_green_le_row/col` (4.10) | `|G_ij|^2 <= 9 Phi sum_k S_ik |G_kj|^2` | none (`S`, `Phi` abstract) | `36 Phi delta^2 <= 1` | 0.5625 <= 1, slack 0.4375 |
| EntryCore `norm_sq_green_le_two_sided`, `norm_sq_green_offdiag_le` (4.11) | `|G_ij|^2 <= 81 Phi^2(...)`, `<= 162 Phi^2 Lambda` | none; `Lambda` abstract (block model `Lambda = 2 max L_{(+,-),(a,b)}` is only in a docstring and in the unported `_blk` forms) | `1 <= Phi`, `36 Phi delta^2 <= 1`, `S_row<=1`, `S_col<=1` | as above |
| EntryCore `ldeQuadRHS_le`, `norm_sq_selfEnergy_err_le` | `<= 38 Phi Lambda`, `|e_i|^2 <= 240 Phi^2 Lambda` | none | `t in [0,1]` | pure constants, no exponent |
| EntryCore:687 `norm_sq_green_diag_sub_le` (4.3) | `|G_ii-m|^2 <= 2160 K^2 Phi^2 Lambda` | none; stability `Stable S (t m^2) K` is an explicit hypothesis | `K delta <= 1/2`, `36 Phi delta^2 <= 1`, `hSrow: sum_k S_ik = 1` | K=1.6193 (instance below), K delta = 0.2024 <= 1/2 |
| EntryCore:793 `norm_condExp_le` | `|x_i| <= K (A+B)` from `Stable S xi K`, `|xi|<=1` | none | `|xi| <= 1` | |xi| = 0.6093, slack 0.3907 |
| EntryCore:818 `norm_sum_coef_green_sub_le` (4.5) | `|sum_k c_k (G_kk-m)| <= B' + K(A+B)` when `sum_k |c_k| <= 1`, `Nonempty n` | none | `sum |c_k| <= 1`, `|xi| <= 1`, `Nonempty n` | LHS 0.0067 <= RHS 0.3363 |

Exponents that change from RBM2D: **none**. Every statement above is `d`-free: no `W^2`, `L^2`, `Z2`, `zdist2`, `Idx`, `scaleM`, `ellT`, `tailT`, `ellStar`, `Meta`, `ellz`, `1/5`, `W^{-2}` token occurs in either file (grep of those tokens in lines 1..845 of EntryCore and of Minor: only the two `import RBM2D...` lines match; output of the script below). The portmap P.7 row for both files lists no dimension token (columns W2/L2/N2/inv2/d=2/Z2/1/5/scal are `-`; `docs/reports/T2015-portmap.md` lines 42 and 64). So the ticket's `d = 2` accounting is: all tokens absent; the file is dimension-free; ST1-COMMON renaming R1-R4 do not apply (no `Sizes`, `Idx`, `Coord` appears).
Constants carried unchanged: 9/4, 9, 36, 81, 162, 38, 240, 2160, `delta <= 1/2`.
Input outside the two files: `RBM.green (H) (z) := (H - z • 1)⁻¹` is defined at `RBM2D/Delocalization.lean:42`, which Minor imports (`import RBM2D.Delocalization`); it is the only declaration of Delocalization.lean used by the kept lines of either file (script output below). Dimension-free, one line. `docs/reports/T2015-portmap.md` has no row for `Delocalization:42`, and the merged `RBM3D/` has no definition of `green` (grep: only comments in `RBM3D/Gauss/DominationAt.lean:39`). The prover must define it in `RBM3D/Green/EntryCore.lean` verbatim (open for the dispatcher: grep of `docs/tickets/*.md`, `docs/reports/T2015-portmap.md`, `docs/reports/T2015-prove.md` for `def green` / `Delocalization:42` finds nothing, so this ticket is where it lands).
Dropped (not ported): only the two `Check` sections (`minor_check_fin2`, `entry_core_check_fin2` and the `chk_*` helpers, which are private `2 x 2` demonstrations), replaced by the `d = 3` instance required by CLAUDE.md §4 step 2. No public declaration is dropped.

### (ii) One concrete nondegenerate instance (d = 3, W = 2, L = 3)

`N = (WL)^d = 216` sites = `L^d = 27` blocks of `W^d = 8`; `S_ab = 1/(7*8)` if the blocks of `a`, `b` are at periodic l1 distance <= 1 (7 neighbour blocks including self), else 0; `H_ab = sqrt(S_ab) g_ab`, `g` complex Hermitian Gaussian sample (seed 2029); `z = 0.1+0.5i`; `m` the root of `m^2+zm+1=0` with `Im m>0`, `xi = m^2`; `x_i = 0.7 (G_ii - m)`; `c` random-sign weights, `sum|c|=1`; `A`,`B`,`B'` are the actual quantities in the hypotheses of `norm_sum_coef_green_sub_le`; `K` is the exact `max->max` norm of `(1-xi S)^-1`, which is what `Stable S xi K` asserts. Hypotheses of Minor:255/242/233: `IsUnit det(H-z)` (det != 0), `G_ii != 0` (min |G_ii| = 0.6104). `n` is nonempty. Script: `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/t2029_check.py` (numpy, 42 lines, no Lean).

Command: `python3 t2029_check.py`
```
d,W,L,N,block size,#nbr blocks: 3 2 3 216 8 7
S row sums in [1.000000000000,1.000000000000]; col sums max 1.000000000000; S_ii=0.017857
Hermitian: True
|det M|>0 (unit): True  min|G_ii|=0.6104
(4.9) max|inv(H^(i)-z)-minorGreen|=2.40e-15
(4.7) |G_ii-(H_ii-z-sum)^-1|=9.01e-16
(4.8) max_j|G_ij+G_ii sum_k H_ik G^(i)_kj|=1.45e-16
m= (-0.0378597706957878+0.7796345881756104j) |m|=0.7806 m^2+zm+1=6.9e-18
|xi|=0.6093 <=1: True
K=||(1-xi S)^-1||_{max->max}=1.6193  (Stable S xi K holds by definition of this norm)
sum|c|= 1.0000000000000002
A=0.1987 B=0.0077 B'=0.0020
norm_sum_coef_green_sub_le: LHS=0.006722 <= RHS=0.336327 : True (slack 0.329605)
norm_condExp_le: max|x_i|=0.212367 <= K(A+B)=0.334310 : True
36*Phi*delta^2=0.5625<=1 (slack 0.4375); delta<=1/2 (slack 0.375); 1-delta=0.875>=1/2; (1+delta)^2=1.2656<=9/4
```
The external probabilistic inputs (`LDERow`, `LDECol`, `LDEQuad`, `Phi`) are `Prop` hypotheses in the endpoint theorems of (4.10)-(4.3), not external theorems; no limit computation is needed, and the key targets named by the ticket (Minor:255, EntryCore:818) do not use them. `GoodEvent`-based statements: at the data `delta=1/8`, `Phi=1`, `K=1` the constants of the `2 x 2` Check of RBM2D already satisfy `36 Phi delta^2 = 0.5625 <= 1`.

Token grep (lines 1..845 of the two sources, regex `W ?\^ ?2|L ?\^ ?2|Z2|zdist2|Idx|scaleM|ellT|tailT|ellStar|Meta|ellz|W⁻²|d = 2|1 / 5|size|Coord|svar|gvar|Sizes|RBM2D`):
```
Minor.txt:7:import RBM2D.Delocalization
Entry.txt:6:import RBM2D.Green.Minor
```
Delocalization names used (8 top-level names tested by `grep -w` in lines 1..845): Minor: `green` only; EntryCore: none.

### Verdicts
- Minor:255 `green_diag_paper` (with 233, 242): PASS (hypotheses hold at the instance; identities verified numerically at N=216).
- EntryCore:818 `norm_sum_coef_green_sub_le` (with 793 `norm_condExp_le`): PASS (all hypotheses hold at the instance; inequality holds with slack 0.3296).
- Every other public declaration: PASS (dimension-free, constants unchanged). Flag for stage 1b and the dispatcher: `RBM.green` (Delocalization:42) is not in RBM3D; define it in this file verbatim (statement-neutral).

## (b) Script output — Sat Oct  3 05:30:28 UTC 2026

Commit on t/T2029: `65181f4 T2029: port Green/EntryCore (resolvent-entry core of lem_GbEXP, minors (4.7)-(4.9)`; `git diff --stat main...t/T2029`:
```
 RBM3D/Green/EntryCore.lean | 1352 ++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1352 insertions(+)
```

$ lake build RBM3D.Green.EntryCore 2>&1 | tail -3
```
Build completed successfully (2680 jobs).
```

$ lake build 2>&1 | tail -1   (full library; the file is not yet imported by the root, the hub adds that at merge)
```
Build completed successfully (3728 jobs).
```

$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Green/EntryCore.lean; echo exit $?
```
exit 1
```

Axioms: script `ax.lean` (collectAxioms over every non-private constant of module RBM3D.Green.EntryCore, run with `lake env lean`):
```
public declarations: 60
declarations with only the three standard axioms: 60 of 60; others: 0
RBM.Green.green_diag_paper : std
RBM.Green.green_off_diag_paper : std
RBM.Green.inv_minor_resolvent : std
RBM.Green.norm_condExp_le : std
RBM.Green.norm_sq_green_diag_sub_le : std
RBM.Green.norm_sq_green_offdiag_le : std
RBM.Green.norm_sum_coef_green_sub_le : std
RBM.green : std
```
(std = only propext, Classical.choice, Quot.sound.)

Target statements, extracted by script (`sed` of the file):
```lean
/-- **(4.7)** in the paper's notation. -/
theorem green_diag_paper (h : IsUnit (H - z • (1 : Matrix n n ℂ)).det) (i : n)
    (hGii : green H z i i ≠ 0) :
    green H z i i = (H i i - z - ∑ k : {a : n // a ≠ i}, ∑ l : {a : n // a ≠ i},
        H i k.1 * minorGreen (green H z) i k l * H l.1 i)⁻¹ := by
  have hsum : (∑ k : {a : n // a ≠ i}, ∑ l : {a : n // a ≠ i},

theorem norm_sum_coef_green_sub_le [Nonempty n] {S : n → n → ℝ}
    {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) {K : ℝ} (hStab : Stable S ξ K) {G : Matrix n n ℂ} {m : ℂ}
    (x : n → ℂ) {A B B' : ℝ}
    (hIBP : ∀ i, ‖x i - ξ * ∑ k, (S i k : ℂ) * (G k k - m)‖ ≤ A)
    (hFA : ∀ i, ‖∑ k, (S i k : ℂ) * ((G k k - m) - x k)‖ ≤ B)
    {c : n → ℝ} (hc : ∑ k, |c k| ≤ 1)
    (hFA' : ‖∑ k, (c k : ℂ) * ((G k k - m) - x k)‖ ≤ B') :
    ‖∑ k, (c k : ℂ) * (G k k - m)‖ ≤ B' + K * (A + B) := by
  have hx := norm_condExp_le hξ hStab x hIBP hFA
```
Endpoint instances (compiled in the same file; hypotheses all discharged, no remaining hypothesis):
```lean
/-- Instance of `green_diag_paper` (4.7) at `H = [[0, 1/8], [1/8, 0]]`, `z = I`, `i = 0`. -/
example : green chkH I 0 0 = (chkH 0 0 - I - ∑ k : {a : Fin 2 // a ≠ 0},
    ∑ l : {a : Fin 2 // a ≠ 0}, chkH 0 k.1 * minorGreen (green chkH I) 0 k l * chkH l.1 0)⁻¹ :=
  green_diag_paper chk_unit 0 (by rw [chk_green]; simp [chkG])

/-- Instance of `green_off_diag_paper` (4.8) at the same data, `j = 1`. -/
example : green chkH I 0 1 = -green chkH I 0 0 * ∑ k : {a : Fin 2 // a ≠ 0},
    chkH 0 k.1 * minorGreen (green chkH I) 0 k ⟨1, by decide⟩ :=
  green_off_diag_paper chk_unit 0 (by rw [chk_green]; simp [chkG]) ⟨1, by decide⟩

/-- Instance of `norm_sum_coef_green_sub_le` (4.5) at `G = chkG`, `m = I`, `ξ = 0`, `x = 0`,
`c ≡ 1/2`, `K = 1`, `A = 0`, `B = B' = 1/65`. -/
example : ‖∑ k, (((fun _ : Fin 2 => (1 / 2 : ℝ)) k : ℝ) : ℂ) * (chkG k k - I)‖
    ≤ 1 / 65 + 1 * (0 + 1 / 65) := by
  have hd : ∀ k : Fin 2, chkG k k - I = ((-(1 / 65) : ℝ) : ℂ) * I := by
    intro k
    fin_cases k <;> simp [chkG] <;> ring_nf
  refine norm_sum_coef_green_sub_le (S := chkS) (ξ := ((0 : ℝ) : ℂ) * I ^ 2)
    (by simp) chk_stable (G := chkG) (m := I) (fun _ => 0) (A := 0) (B := 1 / 65) (B' := 1 / 65)
    (by intro i; simp) ?_ (c := fun _ => 1 / 2) (by simp) ?_
  · intro i
    simp only [hd, sub_zero, ← Finset.mul_sum, Fin.sum_univ_two, chkS]
    norm_num [← two_mul, norm_mul, Complex.norm_real]
  · simp only [hd, sub_zero]
    simp

end Instances

/-- Instance of `norm_sum_coef_green_sub_le` (4.5) on the index set `Zd 3 3` of `d = 3`,
`L = 3` (27 sites): `S ≡ 1/27`, `ξ = 1/2`, `K = 2`, `G = 1`, `m = 0`, `x ≡ 1/2`, `c ≡ 1/27`,
`A = 0`, `B = B' = 1/2`; the conclusion is `1 ≤ 3/2`. -/
example : ‖∑ k : Zd 3 3, (((fun _ : Zd 3 3 => (1 / 27 : ℝ)) k : ℝ) : ℂ)
      * ((1 : Matrix (Zd 3 3) (Zd 3 3) ℂ) k k - 0)‖ ≤ 1 / 2 + 2 * (0 + 1 / 2) := by
  refine norm_sum_coef_green_sub_le (S := zS) (ξ := (1 / 2 : ℂ)) (by simp; norm_num) zstable
    (G := (1 : Matrix (Zd 3 3) (Zd 3 3) ℂ)) (m := 0) (fun _ => 1 / 2) (A := 0) (B := 1 / 2)
    (B' := 1 / 2) ?_ ?_ (c := fun _ => 1 / 27) ?_ ?_
  · intro i
    simp [zS]
  · intro i
    simp [zS]
    norm_num
  · simp
  · simp
    norm_num
end Instance3
end RBM.Green
```
Further instances: the ported `entry_core_check_fin2` (line 1229) applies `norm_sq_green_offdiag_le` and `norm_sq_green_diag_sub_le`; `minor_check_fin2` (line 1086) applies `inv_minor_resolvent`.

Name-clash scan (`/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/clash.sh`):
```
scanned 56 short names against /Users/junyin/Lean_proof/RBM3D/RBM3D (main), clashes: 0
no other 'def green' / namespace Green in main
```

Port provenance: RBM2D at c9a24cf (read with git show). Script diff of the ported ranges against the source:
```
--- diff RBM2D Minor.lean:39-271 vs T2029 lines 39-271
identical
--- diff RBM2D EntryCore.lean:42-844 vs T2029 lines 273-1075
identical
--- diff RBM2D Delocalization.lean:41-42 (green def) vs T2029
/-- The Green's function `G(z) = (H - z)⁻¹`. -/
noncomputable def green (H : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ := (H - z • 1)⁻¹
34:noncomputable def green {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (z : ℂ) :
35-    Matrix n n ℂ := (H - z • 1)⁻¹
36-
--
280:noncomputable def greenMinor (G : Matrix n n ℂ) (i k l : n) : ℂ :=
```
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h   and   diff --stat c9a24cf HEAD -- <the three files>
```
9e0f275
 RBM2D/Delocalization.lean  |  56 ++------------
 RBM2D/Green/EntryCore.lean | 185 ++-------------------------------------------
 RBM2D/Green/Minor.lean     | 116 +++-------------------------
 3 files changed, 23 insertions(+), 334 deletions(-)
```
(RBM2D HEAD has moved past c9a24cf; the port is of c9a24cf as the ticket pins.)
RBM1D: not used.

Narrative (≤ 40 lines):
- `RBM3D/Green/EntryCore.lean` (1352 lines) is one file containing: the `green` definition (RBM2D `Delocalization.lean:42`, the only Delocalization declaration the two files use, flagged in (a); placed in `namespace RBM` ahead of `namespace RBM.Green`, same signature), RBM2D `Green/Minor.lean:39-271` verbatim, RBM2D `Green/EntryCore.lean:42-844` verbatim (script diffs above: identical, so every public statement equals RBM2D's; the only residual difference is the three header imports and the `green` binder placement), then the instance sections.
- Imports: `Mathlib.Analysis.Matrix.Spectrum` and `Mathlib.LinearAlgebra.Matrix.NonsingularInverse` (RBM2D reached `ℂ` through `Delocalization`; the build failed with `OfNat ℂ 0` without the first), and `RBM3D.Defs.Lattice` (for `Zd`, used only by the `d = 3` instance; no ST-2 .. ST-6 file, not `RBM3D`).
- `d = 2` accounting (ST1-COMMON item 2): none of the portmap tokens occurs in the two files (grep in (a)); the file is `d`-free; R1-R4 do not apply. No scale (`scaleM`, `ellT`, ...) occurs.
- Dropped: nothing public. The two RBM2D `Check` sections are kept as compiled instances (private `chk_*`, `minor_check_fin2`, `entry_core_check_fin2`, without their `#print axioms` lines, copied from `Minor.lean:273-315` and `EntryCore.lean:846-976`).
- Instances added: `green_diag_paper` and `green_off_diag_paper` at `H = [[0,1/8],[1/8,0]]`, `z = I`, `i = 0` (nonzero off-diagonal, `det(H - z) = -65/64`, `G_00 = 64/65 I`); `norm_sum_coef_green_sub_le` at the same `G`, `m = I`, `c ≡ 1/2`, `K = 1`; and at `n = Zd 3 3` (27 sites, `d = 3`, `L = 3`) with `S ≡ 1/27`, `ξ = 1/2`, `K = 2` (stability proved in `zstable` by a max argument), `G = 1`, `m = 0`, `x ≡ 1/2`, `c ≡ 1/27`, conclusion `1 ≤ 3/2`. All deterministic hypotheses are discharged; the `LDE*`/`Stable` hypotheses of the ported check are proved on the concrete data. These index types (`Fin 2`, `Zd 3 3`) are not the MD-1 `Sizes` sequence or the probe's `sz0`/`sz1`: the statements are over an arbitrary finite index type, so the instances fix `n` only; the full-model block data of (a)(ii) (`N = 216`) is not instantiated in Lean.
- `norm_sq_green_diag_sub_le` etc. take the probabilistic inputs as the `Prop`s `LDERow/LDECol/LDEQuad` (RBM2D design, unchanged).
- No `sorry`/`admit`/`axiom`/`native_decide`; no linter warning in the build output of the module.

## (c) Verified Mathlib names (all used in the compiled file)
`Matrix.inv_eq_left_inv`, `Matrix.det_fin_two`, `Matrix.nonsing_inv_mul`, `Matrix.mul_nonsing_inv`, `Finite.exists_max`, `norm_sum_le`, `norm_sub_norm_le`, `ZMod.card`, `Finset.mul_sum`, `two_mul`, `isUnit_iff_ne_zero`, `Complex.norm_real`; import `Mathlib.Analysis.Matrix.Spectrum` is required for `ℂ` in this file (build error without it).

## (d) Open issues and paper-delta candidates
- Open for the dispatcher: `RBM.green` (RBM2D `Delocalization.lean:42`) now lives in this file (portmap has no row for it); later tickets needing it import `RBM3D.Green.EntryCore`. If a later ST-1 file also copies it, it would clash.
- Root import `import RBM3D.Green.EntryCore` is to be added by the hub at merge (the full `lake build` above does not yet include the module).
- Paper-delta candidates: none (statements are RBM2D's verbatim and `d`-free; the paper does not restate them, it cites [YY_25] Lemma 4.2).

## Amend 1 (repairer claude-opus-5-5, Sat Oct  3 05:48:58 UTC 2026; ticket Amend 1, CONTROL H23 (a), DECISIONS §20)

Branch t/T2029: 65181f4 -> 739783a. Only `RBM3D/Test/Axioms.lean` changed; `RBM3D/Green/EntryCore.lean` unchanged by hash.
```
$ git diff --stat 65181f4 739783a
 RBM3D/Test/Axioms.lean | 7 ++++++-
 1 file changed, 6 insertions(+), 1 deletion(-)
$ git rev-parse 65181f4:RBM3D/Green/EntryCore.lean 739783a:RBM3D/Green/EntryCore.lean
60944aa76808f09a067a95ba8b6f392699da88bd
60944aa76808f09a067a95ba8b6f392699da88bd
$ git diff 65181f4 739783a
diff --git a/RBM3D/Test/Axioms.lean b/RBM3D/Test/Axioms.lean
index 02b1d20..a79fbba 100644
--- a/RBM3D/Test/Axioms.lean
+++ b/RBM3D/Test/Axioms.lean
@@ -105,7 +105,12 @@ def structuralProps : List Name :=
    `RBM.Gauss.Sizes.Bandwidth, -- `(Main_DEL_COND)`: `W ≥ N^𝔠`
    `RBM.Gauss.Sizes.SizeTendsto, -- `N → ∞` along the size sequence
    `RBM.Gauss.Sizes.Admissible, -- the standing hypotheses of the main results
-   `RBM.Gauss.Sizes.locDomain] -- the spectral domain `𝐃_{κ,ε}`
+   `RBM.Gauss.Sizes.locDomain, -- the spectral domain `𝐃_{κ,ε}`
+   `RBM.Green.GoodEvent,      -- the event Ω of (4.10): every entry of `G` within `δ` of `m·I`
+   `RBM.Green.LDERow,         -- row large-deviation event, input of `lem_GbEXP` (later ST-1)
+   `RBM.Green.LDECol,         -- column large-deviation event, input of `lem_GbEXP` (later ST-1)
+   `RBM.Green.LDEQuad,        -- quadratic large-deviation event; h.p. bound S1-19 `stochDom_ldeQuad`
+   `RBM.Green.Stable]         -- stability of `1 − ξS` with constant `K`; band profile S1-24
 
 /-- The premises the audit reports on: borrowed plus owed. -/
 def interfaceProps : List Name := borrowedProps ++ owedProps
```

Registry pre-check (DECISIONS §20 (2)), scratch file outside the repo, after `lake build RBM3D.Green.EntryCore` ("Build completed successfully (2680 jobs)."):
```
$ cat /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2029-precheck.lean
import RBM3D
import RBM3D.Green.EntryCore

#assert_rbm_axioms
$ lake env lean /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2029-precheck.lean; echo exit $?   (lines 1, 20 of output)
axiom audit: 1086 theorems, 415 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 14 (borrowed 3, owed 1, structural 10).
exit 0
$ grep -c 'RBM.Green' <output>   (no Green name in the 'carry nothing yet' list, no 'unregistered' error)
0
```

Full build in the worktree at 739783a (root does not yet import EntryCore; the hub adds it at merge):
```
$ lake build 2>&1 | grep -n "axiom audit:\|premises found\|Build completed\|error"
88:info: RBM3D.lean:70:0: axiom audit: 1041 theorems, 400 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
107:premises found by scanning: 9 (borrowed 3, owed 1, structural 5).
131:Build completed successfully (3728 jobs).
exit 0
```
Note for the merge: `git diff 65181f4 main -- RBM3D/Test/Axioms.lean | grep '^@@'` gives hunks `@@ -72,11 +72,11 @@` (`borrowedProps`) and `@@ -124,9 +124,7 @@` (`certificates`), none in `structuralProps` (lines 95-108 at 65181f4); H23 (b) applies if git reports a conflict.
