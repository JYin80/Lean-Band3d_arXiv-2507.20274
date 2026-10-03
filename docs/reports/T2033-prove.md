Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 15:18:24 UTC 2026

Scratch scripts (outside the repository, no Lean): `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2033`, files `$S/chk.py`, `$S/lm.py`, `$S/h0.py`.
Source read: `git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Induction/Split.lean` (952 raw lines; the portmap's "818" is the kept-line count; its line numbers 385/529/635/692 match the c9a24cf text).
Setting of every target: fixed deterministic Hermitian `H` on `Vtx d L W = Zd d L × Fin (W^d)`, `[NeZero L] [NeZero W]`, spectral parameter `z`; no probability.

### (i) Exponent table

| # | Quantity (RBM2D c9a24cf line) | RBM2D | RBM3D (d >= 3) | Constraint | Slack |
|---|---|---|---|---|---|
| 1 | block weight `bw`, `Eblk` entry (Split:176,184) | `(W:ℝ)⁻¹ ^ 2` | `((W:ℝ)^d)⁻¹`, equal to merged `Eblk` entry `((W:ℂ)^d)⁻¹` (`Loop/GLoop.lean:55`); cast `((↑(W^d)⁻¹):ℂ)` by `Complex.ofReal_inv/_pow` | equals the `Eblk` entry | 0 (identity) |
| 2 | `sum_bw`: ∑_p bw b p = 1 (Split:624) | block `Fin W × Fin W`, card `W^2`, proof uses `pow_two` | block `Fin (W^d)`, card `W^d`, `W^d · (W^d)⁻¹ = 1` needs `W ≠ 0` (`NeZero W`) | = 1 exactly | 0; at d=3,W=2: 8·(1/8)=1 (script: with the RBM2D weight `W⁻²` the sum would be 2) |
| 3 | `norm_Eblk_le` (Split:615) | `‖E_b‖ ≤ (W⁻¹)^2` | `‖E_b‖ ≤ ((W:ℝ)^d)⁻¹`; merged public `norm_Eblk_le_inv_W_sq` (`Gauss/FlowCalculus.lean:663`) gives it | = at the block | 0 (tight, script: 0.125) |
| 4 | `norm_Gsig_le` (Split:604) | `‖G_σ‖ ≤ \|Im z\|⁻¹`, via `Gauss.norm_green_le` | dimension-free; merged `norm_Gsig_le_inv_eta` (`FlowCalculus.lean:644`, hyp `η ≤ \|z.im\|`, `0<η`) at `η = \|z.im\|` | `z.im ≠ 0` | script: ‖G‖ = 1.99987 ≤ 2 = 1/η |
| 5 | `norm_gchain_le` (Split:650), chain with `\|σ\| = \|a\|+1` | `\|Im z\|^{-\|σ\|} ((W⁻¹)^2)^{\|a\|}` | `\|Im z\|^{-\|σ\|} (((W:ℝ)^d)⁻¹)^{\|a\|}` | induction: `(η⁻¹ W^{-d})·(η⁻¹)^{\|σ'\|}(W^{-d})^{\|a'\|}` closes by `ring` | 0 |
| 6 | (5.2) `norm_gloop_le_opNorm` (Split:678) and **key** `norm_gloop_le_of_le_abs_im` (Split:692), `n ≥ 1`, `σ.length = a.length` | `η⁻¹^n ((W⁻¹)^2)^(n-1)` | `η⁻¹^n (((W:ℝ)^d)⁻¹)^(n-1)`, `0<η ≤ \|z.im\|` | `n-1` copies of `E`, one is absorbed by the trace (row 7) | 0: attained at `H=0, z=i, W=2, d=3, n=4`: loop = 2⁻⁹ = bound (script h0) |
| 7 | **key** `split_norm_trace_mul_Eblk_le` (Split:635): `‖tr(M E_b)‖ ≤ ‖M‖_op` | uses `sum_bw`, `‖M p p‖ ≤ ‖M‖` | same statement; proof via `sum_bw` (row 2) | constant 1 | script: 0.00344 ≤ 0.2047 |
| 8 | (5.115)/(5.116) `norm_sq_gloop_le_symIdx` (:375), **key** `norm_gloop_symIdx_split_le` (:385): Cauchy–Schwarz for `wmass u v X = ∑ u_i v_j \|X_ij\|²` | dimension-free algebra (weights `bw`) | dimension-free; only `bw` of row 1 enters | constant 1 | script (labels all `b0`, W=2,d=3,L=3): (5.115) 6.199e-10 ≤ 6.657e-10; (5.116) 1.301e-10 ≤ 6.657e-10 |
| 9 | (5.117) `loopMax_two_mul_add_le` (:513), `l₁,l₂ ≥ 1`, `l₁+l₂=n+1`; `_two_mul_add_two_le` (:520) | `max\|L^{2n+2}\| ≤ max\|L^{2l₁}\| max\|L^{2l₂}\|` | identical (`loopMax` over `Fin n → Bool` × `Fin n → Zd d L`, finite) | constant 1 | script d=3,W=2,L=3,η=.5: loopMax₄ = 3.687e-4 ≤ loopMax₂² = 2.603e-3 |
| 10 | **key** (6.4) `loopMax_odd_sq_le` (:529), `m ≥ 1` | `(max\|L^{2m+1}\|)² ≤ max\|L^{2m}\| max\|L^{2m+2}\|` | identical, dimension-free | constant 1 | script m=1: 1.7474e-5 ≤ 1.8811e-5 (ratio 0.93) |
| 11 | (5.118) `loopXi_le` (:569): `Ξ_m = loopMax_m · A^{m-1}` | `Ξ_{2n+2} ≤ Ξ_{2l₁}Ξ_{2l₂}·A`, `A ≥ 0` | identical; `A` is a free parameter (only the docstring at :562 says `A = W²ℓ_u²η_u`: docstring token, replace by "scale parameter") | exponent `(2n+2-1) = (2l₁-1)+(2l₂-1)+1` since `l₁+l₂ = n+1` | 0 (equality, `omega`) |
| 12 | Lemma 6.1 `sum_norm_inner_sq_le_trace_{rpow,pow}` (:799,:821) with `re_dotProduct_mulVec_le`, `trace_cfc_eq_sum`, `sum_norm_inner_sq_le_of_eigenvalues_le` | generic `ι`, `E` | unchanged (no `W`, `L`, `d`) | `p ≥ 1` | n/a |

`d = 2` token accounting (portmap P.6 rows `Induction/Split:` = 9 `inv2` rows: 176, 184, 615, 652, 664, 671, 672, 680, 695): all nine are the block weight `(W:ℝ)⁻¹ ^ 2` and become `((W:ℝ)^d)⁻¹` (rows 1, 3, 5, 6). Not listed by the portmap but d = 2 dependent, to be replaced: `sum_bw` proof (`Fin W × Fin W`, `pow_two`, :624-633); `BlockIndex L W` → `Vtx d L W`; `Z2 L` → `Zd d L`; `LoopIdx (Z2 L)` → `Loop.LoopIdx (Zd d L)`; `Gsig` → merged `Gres`; `gloop L W H z I` → `loopL d L W H z I` (`Loop/GLoopFlow.lean:123`), `gloopProd` is public (`GLoopFlow.lean:384`); `green H z` → `Gres H z true`; docstrings at :13-20, :24-25, :49, :173-174, :562, :614, :649, :676, :691. Dimension-free (no change): rows 4, 8-12, `wmass*`, `trace_mul_diagonal_*`, `symIdx`, `exists_split_*`, `loopMax_le/_nonneg`.
The adjoint identity `(Gres H z σ)ᴴ = Gres H z (!σ)` exists only as private lemmas in merged files (`Induction/Contract.lean:223` `Gres_conjTranspose`, `Green/Pins.lean:367` `gres_false`): copy RBM2D `Gsig_conjTranspose` (`Hierarchy/Loops.lean`) as a private helper. `gloopProd_append` is private in `GLoopFlow.lean:401` (and a private copy in `ContractionBasic.lean:774`): copy as private (ST1-COMMON item 4/5).
Name clash: `RBM.Gauss.loopMax` exists (`Loop/GLoop.lean:102`, argument `ω E t`); RBM2D's `RBM.Ind.loopMax L W H z n` has a different full name (`RBM.Ind` is an existing namespace, e.g. `ScaleFacts.lean:150`), but the short name coincides: prover must grep and say which name is used (consumers S1-18, S1-31, S1-35, S1-36 take it).
Public declarations: none dropped. The portmap P.3 table has no Split rows (Split was an ST-3 file), so no declaration is marked unused; the 19 names with no user outside Split in RBM2D (script: `git grep -w` over c9a24cf; e.g. `exists_split_chainIdx`, `gchain_append`, `gchain_append_one`, `gloop_append_eq_trace`, `loopMax_two_mul_add_two_le`, `norm_gloop_symIdx_le_loopMax_mul`, `norm_gloop_symIdx_split_le` [key], `norm_sq_trace_Eblk_le`, `norm_trace_Eblk_split_le`, the matrix engine `wmass_*`/`trace_mul_diagonal_*`/`re_dotProduct_mulVec_le`/`trace_cfc_eq_sum`/`sum_norm_inner_sq_le_{of_eigenvalues_le,trace_rpow}`) are internal links of the key chain or paper variants: all ported.
RBM2D's own instances at the end of Split (:840-900) are `W = 1` and false at `W = 2`: `Eblk * Eblk = Eblk` holds only for `W = 1` (general: `E_b² = E_b/W^d`), and "loop (G E_0)^4 has modulus 1" becomes `W^{-3d}`; both instances must be recomputed at `W = 2` (script h0 below).

### (ii) One concrete nondegenerate instance: d = 3, W = 2, L = 3

`N = (W L)^d = 216`, block size `W^d = 8`, `3^3 = 27` labels; `H` a random 216×216 Hermitian matrix (GUE-like, entries/√(2N)), `z = 0.3 + 0.5i` so `|Im z| = η = 0.5` (hypothesis `η ≤ |Im z|` with equality, `0 < η`, `z.im ≠ 0`), `NeZero 3`, `NeZero 2`, loops of length `n ≥ 1` with `σ.length = a.length`. No external hypothesis occurs (all targets are deterministic, no limit computation needed). Commands and verbatim output:

```
$ python3 $S/chk.py
sum_bw = 1.0 (W^d weight)  ; with RBM2D weight W^-2: 2.0
||E_b||_op = 0.125  (W^d)^-1 = 0.125
max ||G||_op = 1.9998703904973911  <= 1/eta = 2.0
(5.2) |L| <= eta^-n (W^-d)^(n-1) on 200 random loops: True  max ratio 0.3067762799625621
split trace: 0.0034395487711226472 <= 0.20468736285423222
(5.115) lhs 6.199152927684115e-10 <= rhs 6.657339325072836e-10 True
(5.116) 1.3006345598735478e-10 <= 6.657339325072836e-10 True
$ python3 $S/lm.py          # exact loopMax_k over all 2^k signs and 27^k labels, k = 2,3,4
loopMax_2, _3, _4 = {2: np.float64(0.05101536658584081), 3: np.float64(0.004180150932967264), 4: np.float64(0.0003687388815923853)}
(6.4) m=1: loopMax_3^2 = 1.7473661822387085e-05 <= loopMax_2*loopMax_4 = 1.8811349218888487e-05 True
(5.2) loopMax_k <= eta^-k (W^-d)^(k-1): {2: np.True_, 3: np.True_, 4: np.True_}
(5.117) loopMax_4 <= loopMax_2*loopMax_2 (n=1,l1=l2=1): 0.0003687388815923853 <= 0.0026025676278877232 True
$ python3 $S/h0.py          # H = 0, z = i, label 0
G(+) = i*1: True
tr E_0 = 1.0 ; E_0^2 = E_0/W^d: True ; E_0^2 = E_0: False
tr (G E_0)^4 = (0.001953125+0j)  = W^(-3d) = 0.001953125 ; (5.2) bound eta^-4 (W^-d)^3 = 0.001953125
```

Reading: with the exponent `d` in the block weight, row 2 gives 1 (the `d = 2` weight gives 2), rows 3 and 6 are tight (equality at `H = 0`), and the odd-length inequality (6.4) holds non-trivially (ratio 0.93, all values nonzero). A Lean instance may use `H = 0`, `z = i` (Hermitian, `|Im z| = 1`): then `loopMax 4 ≥ 2⁻⁹` and the instance of `loopXi_le` at `A = 1` is nonvacuous.

### Verdicts

- `loopMax_odd_sq_le` (Split:529): PASS (dimension-free; every hypothesis `1 ≤ m`, Hermitian `H`, `NeZero L` holds at the instance).
- `split_norm_trace_mul_Eblk_le` (Split:635): PASS (only the weight of row 1 and `sum_bw` change).
- `norm_gloop_le_of_le_abs_im` (Split:692): PASS (exponent `2 → d` of row 6 closes with slack 0, tight at the instance).
- `norm_gloop_symIdx_split_le` (Split:385): PASS (dimension-free).
- Overall: PASS; no missing input.

### (a′) Preflight corrections — Sat Oct  3 15:39:56 UTC 2026

Three citations of (a) differ from the files, none changes a verdict: the private `Gres_conjTranspose` is at `Induction/Contract.lean:224` (223 is its docstring), and that file is in `main` (86368fa), not in this branch's base eb6d67a; the private copy of `gloopProd_append` in `Hierarchy/ContractionBasic.lean:774` is named `contraction_gloopProd_append`.

## (b) Script output — Sat Oct  3 15:39:56 UTC 2026 (branch `t/T2033`, HEAD `22d4235`; `$S` = the T2033/ directory of the session scratchpad)

```
$ lake build RBM3D.Induction.Split 2>&1 | tail -2
Build completed successfully (3297 jobs).
$ lake build 2>&1 | tail -1                  # whole library with the root #assert_rbm_axioms
Build completed successfully (3775 jobs).
$ git diff main...t/T2033 --stat
 RBM3D/Induction/Split.lean | 1097 ++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1097 insertions(+)
$ grep -c "sorry\|admit\|native_decide" RBM3D/Induction/Split.lean; grep -c "^axiom" RBM3D/Induction/Split.lean
0
0
$ lake env lean $S/axcopy.lean | grep axioms     # copy of the file + #print axioms of the 4 targets and the 11 `check_*` instances
'loopMax_odd_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'split_norm_trace_mul_Eblk_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'norm_gloop_le_of_le_abs_im' depends on axioms: [propext, Classical.choice, Quot.sound]
'norm_gloop_symIdx_split_le' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean $S/axcopy.lean | grep -c "check_.*\[propext, Classical.choice, Quot.sound\]"
11
$ lake env lean $S/axall.lean | grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]"     # #print axioms of all 56 public names
53
$ lake env lean $S/axall.lean | grep -v "Classical.choice, Quot.sound"
'RBM.Ind.symIdx' does not depend on any axioms
'RBM.Ind.symIdx_σ_length' depends on axioms: [propext]
'RBM.Ind.symIdx_a_length' depends on axioms: [propext]
```

Targets (`python3 $S/extract.py <names>`: the file's text from the declaration to `:=`). Section variables in force: `Split.lean:388/510 variable {d L W : ℕ} [NeZero L]`, `:677` adds `[NeZero W]`, `:518/:712 variable {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ}`; `‖·‖` on matrices is the `ℓ²` operator norm (`open scoped Matrix.Norms.L2Operator`, section `OpNorm`).
```
-- RBM3D/Induction/Split.lean:598
theorem loopMax_odd_sq_le (hH : H.IsHermitian) {m : ℕ} (hm : 1 ≤ m) :
    loopMax d L W H z (2 * m + 1) ^ 2
      ≤ loopMax d L W H z (2 * m) * loopMax d L W H z (2 * m + 2) :=
-- RBM3D/Induction/Split.lean:700
theorem split_norm_trace_mul_Eblk_le (M : Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (b : Zd d L) :
    ‖trace (M * Eblk d L W b)‖ ≤ ‖M‖ :=
-- RBM3D/Induction/Split.lean:757
theorem norm_gloop_le_of_le_abs_im (hH : H.IsHermitian) {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (I : Loop.LoopIdx (Zd d L)) (hwf : I.σ.length = I.a.length)
    (hn : 1 ≤ I.a.length) :
    ‖loopL d L W H z I‖ ≤ η⁻¹ ^ I.a.length * (((W : ℝ) ^ d)⁻¹) ^ (I.a.length - 1) :=
-- RBM3D/Induction/Split.lean:454
theorem norm_gloop_symIdx_split_le (hH : H.IsHermitian) {σ₁ σ₂ : List Bool}
    {a₁ a₂ : List (Zd d L)} (h₁ : σ₁.length = a₁.length + 1) (h₂ : σ₂.length = a₂.length + 1)
    (c b' b : Zd d L) :
    ‖loopL d L W H z (symIdx (σ₁ ++ σ₂) (a₁ ++ c :: a₂) b' b)‖
      ≤ ‖loopL d L W H z (symIdx σ₁ a₁ c b)‖ * ‖loopL d L W H z (symIdx σ₂ a₂ b' c)‖ :=
```

Compiled nonempty instances at `d = 3`, `L = 3`, `W = 2` (`N = 216`), `H = 0`, `z = i`, `η = 1 = |Im z|` (`python3 $S/chk_extract.py full <names>`; private theorems of section `Checks`; every hypothesis discharged: `Matrix.isHermitian_zero`, `1 ≤ m`, `0 < η`, `η ≤ |z.im|`, `hwf`, `1 ≤ a.length`, the length equations by `rfl`):
```
-- Split.lean:1006
private theorem check_odd_sq_le :
    loopMax 3 3 2 (0 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) Complex.I (2 * 1 + 1) ^ 2
      ≤ loopMax 3 3 2 (0 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) Complex.I (2 * 1)
        * loopMax 3 3 2 (0 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) Complex.I (2 * 1 + 2) :=
  loopMax_odd_sq_le Matrix.isHermitian_zero le_rfl
-- Split.lean:1022
private theorem check_trace_mul_Eblk_le :
    ‖trace ((1 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) * Eblk 3 3 2 (0 : Zd 3 3))‖
      ≤ ‖(1 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ)‖ :=
  split_norm_trace_mul_Eblk_le _ _
-- Split.lean:1035
private theorem check_gloop_le_of_le_abs_im :
    ‖loopL 3 3 2 (0 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) Complex.I
        ⟨[true, true, true, true], [0, 0, 0, 0]⟩‖
      ≤ (1 : ℝ)⁻¹ ^ 4 * (((2 : ℝ) ^ 3)⁻¹) ^ (4 - 1) :=
  norm_gloop_le_of_le_abs_im Matrix.isHermitian_zero one_pos (by simp) _ rfl (by simp)
-- Split.lean:1056
private theorem check_symIdx_split_le :
    ‖loopL 3 3 2 (0 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) Complex.I
        (symIdx ([true] ++ [true]) (([] : List (Zd 3 3)) ++ (0 : Zd 3 3) :: []) 0 0)‖
      ≤ ‖loopL 3 3 2 (0 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) Complex.I
            (symIdx [true] ([] : List (Zd 3 3)) (0 : Zd 3 3) 0)‖
        * ‖loopL 3 3 2 (0 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) Complex.I
            (symIdx [true] ([] : List (Zd 3 3)) (0 : Zd 3 3) 0)‖ :=
  norm_gloop_symIdx_split_le Matrix.isHermitian_zero rfl rfl 0 0 0
```
Nondegeneracy at the same data (statements by `chk_extract.py stmt`; also in the file: check_trace_mul_Eblk_ne_zero, check_loopMax_two_mul_add_le, check_loopXi_le):
```
-- Split.lean:999
private theorem check_loopMax_formula (n : ℕ) (hn : 1 ≤ n) :
    loopMax 3 3 2 (0 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) Complex.I n
      = (((2 : ℝ) ^ 3)⁻¹) ^ (n - 1) :=
-- Split.lean:1014
private theorem check_odd_sq_le_values :
    loopMax 3 3 2 (0 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) Complex.I (2 * 1 + 1) = 1 / 64 ∧
    loopMax 3 3 2 (0 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) Complex.I (2 * 1) = 1 / 8 ∧
    loopMax 3 3 2 (0 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) Complex.I (2 * 1 + 2) = 1 / 512 :=
-- Split.lean:1043
private theorem check_gloop_attained :
    ‖loopL 3 3 2 (0 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) Complex.I
        ⟨[true, true, true, true], [0, 0, 0, 0]⟩‖ = 1 / 512 :=
-- Split.lean:1067
private theorem check_symIdx_split_values :
    ‖loopL 3 3 2 (0 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) Complex.I
        (symIdx ([true] ++ [true]) (([] : List (Zd 3 3)) ++ (0 : Zd 3 3) :: []) 0 0)‖ = 1 / 512 ∧
    ‖loopL 3 3 2 (0 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) Complex.I
        (symIdx [true] ([] : List (Zd 3 3)) (0 : Zd 3 3) 0)‖ = 1 / 8 :=
```

```
$ python3 $S/clash.py      # declaration lines of the 56 new public names over the 97 .lean files of the main worktree (at 31476de)
main-worktree files scanned: 97 | new public names: 56
declaration-line hits of a new public name outside Split.lean: [('loopMax', 'Loop/GLoop.lean')]
$ python3 $S/stmtdiff.py   # RBM2D c9a24cf signatures up to `:=`, renamed (BlockIndex L W→Vtx d L W, Z2 L→Zd d L, gloop L W→loopL d L W, Gsig→Gres, LoopIdx (→Loop.LoopIdx (, (W:ℝ)⁻¹^2→((W:ℝ)^d)⁻¹, gchain/Eblk/gloopProd/loopMax/loopXi L W→… d L W), against this file
RBM2D public declarations: 56
RBM3D public declarations (incl. Checks lemmas): 56
RBM2D names missing from RBM3D: []
RBM3D public names not in RBM2D: []
--- RESIDUAL DIFF: symIdx
   2D->3D: replace | {L |=>| {d L
--- RESIDUAL DIFF: norm_Gsig_le
   2D->3D: replace | norm_Gres_le |=>| norm_Gsig_le
identical after renaming: 54 of 56
$ python3 $S/tok.py        # the nine portmap P.6 `inv2` rows of Induction/Split: RBM2D line | RBM3D line | RBM3D text; then the leftover-token scan
portmap P.6 inv2 rows of Induction/Split (RBM2D c9a24cf line | RBM3D line | RBM3D text):
  176 | 186      | if p.1 = b then ((W : ℝ) ^ d)⁻¹ else 0
  184 | 194      | have hcast : ((((W : ℝ) ^ d)⁻¹ : ℝ) : ℂ) = ((W : ℂ) ^ d)⁻¹ := by
  615 | 681      | theorem norm_Eblk_le (b : Zd d L) : ‖Eblk d L W b‖ ≤ ((W : ℝ) ^ d)⁻¹ := by
  652 | 717      | ‖gchain d L W H z σ a‖ ≤ |z.im|⁻¹ ^ σ.length * (((W : ℝ) ^ d)⁻¹) ^ a.length := by
  664 | 729      | pow_succ' (((W : ℝ) ^ d)⁻¹)]
  671 | 736      | ≤ |z.im|⁻¹ * (((W : ℝ) ^ d)⁻¹) *
  672 | 737      | (|z.im|⁻¹ ^ σ.length * (((W : ℝ) ^ d)⁻¹) ^ a.length) := by
  680 | 745      | ‖loopL d L W H z I‖ ≤ |z.im|⁻¹ ^ I.a.length * (((W : ℝ) ^ d)⁻¹) ^ (I.a.length - 1) := by
  695 | 760      | ‖loopL d L W H z I‖ ≤ η⁻¹ ^ I.a.length * (((W : ℝ) ^ d)⁻¹) ^ (I.a.length - 1) := by
remaining d=2 tokens in the new file (code, comments stripped of the docstring of the port note):
   ⁻¹ \^ 2 -> []
   W \^ 2 -> []
   Z2 -> []
   BlockIndex -> []
   Gsig H -> []
   \bgloop L W -> []
$ sed -n '690p;696,697p' RBM3D/Induction/Split.lean     # sum_bw (RBM2D: block Fin W × Fin W, `pow_two`)
690: theorem sum_bw (b : Zd d L) : ∑ p : Vtx d L W, bw b p = 1 := by
696:   field_simp
697:   exact Nat.cast_pow W d
$ lake env lean $S/registry.lean; echo $?     # `import RBM3D`, `import RBM3D.Induction.Split`, `#assert_rbm_axioms`
registry exit: 0
$ diff $S/registry.out $S/registry_base.out   # base: the same file without the Split import
1c1
< axiom audit: 1916 theorems, 822 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
---
> axiom audit: 1863 theorems, 816 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
diff exit: 1
$ grep -c 'def .*: Prop' RBM3D/Induction/Split.lean
0
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Induction/Split.lean      # RBM2D HEAD = 9e0f275
 RBM2D/Induction/Split.lean | 142 ++-------------------------------------------
 1 file changed, 4 insertions(+), 138 deletions(-)
```

**Narrative.**
- Source: RBM2D `Induction/Split.lean` at `c9a24cf` (952 raw lines), ported to `RBM3D/Induction/Split.lean` (1097 lines, namespace `RBM.Ind` as in RBM2D, `open Matrix RBM.Gauss`). Only that file is touched; `RBM3D/Test/Axioms.lean` and `RBM3D.lean` are not (root import: hub, at merge).
- Coverage: all 56 public declarations of the RBM2D file are ported, none dropped (script: nothing missing, nothing extra); the portmap has no unused-mark for Split (section (a), "Public declarations"). 54 signatures are identical after the renaming; the two residual lines are artifacts of the diff script (binder `{d L`, and the rename hitting the name `norm_Gsig_le`).
- Renaming (ST1-COMMON item 2): `BlockIndex L W→Vtx d L W`, `Z2 L→Zd d L`, `Gsig→Gres`, `gloop→loopL` (list-based, `GLoopFlow.lean:123`), `LoopIdx→Loop.LoopIdx`, `L W→d L W` on `gchain/Eblk/gloopProd/loopMax/loopXi`, `(W⁻¹)^2→(W^d)⁻¹`. Nine `inv2` rows of P.6 and `sum_bw` are the d = 2 content; the scan finds no leftover token. `green`, `Gauss.norm_green_le` are not used.
- Reuse of merged text: `norm_Gsig_le` is `norm_Gsig_le_inv_eta` (`FlowCalculus.lean:644`) at `η = |z.im|`; `norm_apply_le_l2_opNorm` is `norm_matrix_entry_le_opNorm` (`FlowCalculus.lean:591`); `Eblk_isHermitian` gives `Eblk_conjTranspose`. The other proofs are RBM2D's, with `W^d` for the block (`sum_bw`, `Eblk_eq_diagonal_bw` cast by `push_cast`).
- Private copies (CLAUDE §3 E): `Gres_conjTranspose` (text of `Contract.lean:224` in main), `gloopProd_nil/cons/append` (`GLoopFlow.lean:391-401`), `loopL_eq_trace`; for the instances `Gres_zero_I`, `Eblk_mul_self`, `gloopProd_zero_I`, `norm_loopL_zero_I`, `loopMax_zero_I`.
- The merged `Gauss.norm_gloop_le_sharp` (`GLoopFlow.lean:866`) states the same bound as `norm_gloop_le_of_le_abs_im` with `I.WF` for `hwf`; it is not used, the RBM2D chain (`norm_gchain_le`, `norm_gloop_le_opNorm`) is ported.
- Name `loopMax`: this file declares `RBM.Ind.loopMax` (RBM2D's name); `RBM.Gauss.loopMax` (`Loop/GLoop.lean:102`, arguments `ω E t n`) is a different declaration and the only declaration-line hit of the clash scan. Consumers (S1-18, S1-31, S1-35, S1-36) must qualify the name.
- Instances: `H = 0`, `z = i` (so `G(±) = ±i·1`), loops with all labels `0`: `loopMax 3 3 2 0 i n = ((2^3)⁻¹)^(n-1)` for all `n ≥ 1` (`check_loopMax_formula`, general lemma `loopMax_zero_I`). Hence the odd-length instance is (1/64)² ≤ (1/8)(1/512), an equality, with all values nonzero; `norm_gloop_le_of_le_abs_im` is attained (1/512); the symmetric split reads 1/512 ≤ (1/8)(1/8). The random 216×216 instance of (a) (ii) is numeric only; the Lean instances use the `H = 0` choice that (a) allows. RBM2D's own `Checks` (`W = 1`) are not ported; (a) records that they fail at `W = 2`.
- Registry: the file has no `Prop`-valued definition, so no line is added to `RBM3D/Test/Axioms.lean`; the pre-check exits 0 and only the theorem/definition counts change (1863→1916, 816→822).

## (c) Verified names — Lean resolution (`#where` elaborator over `resolveGlobalConst`, `$S/where.lean`), name -> full name [module]
- Matrix.nonsing_inv_eq_ringInverse [Mathlib.LinearAlgebra.Matrix.NonsingularInverse]
- Matrix.conjTranspose_nonsing_inv [Mathlib.LinearAlgebra.Matrix.NonsingularInverse]
- Matrix.diagonal_mul_diagonal [Mathlib.Data.Matrix.Mul]
- Matrix.smul_apply [Mathlib.LinearAlgebra.Matrix.Defs]
- Matrix.mul_smul [Mathlib.Data.Matrix.Mul]
- Matrix.isHermitian_zero [Mathlib.LinearAlgebra.Matrix.Hermitian]
- Matrix.trace_smul [Mathlib.LinearAlgebra.Matrix.Trace]
- smul_mul_assoc [Mathlib.Algebra.Group.Action.Defs]
- smul_smul [Mathlib.Algebra.Group.Action.Defs]
- List.eq_nil_or_concat' [Mathlib.Data.List.Basic]
- List.norm_prod [Mathlib.Analysis.Normed.Ring.Basic]
- Complex.conj_I [Mathlib.Basic.Complex.Basic]
- Complex.I_ne_zero [Mathlib.Basic.Complex.Basic]
- Complex.norm_natCast [Mathlib.Analysis.Complex.Norm]
- Matrix.l2_opNorm_diagonal [Mathlib.Analysis.CStarAlgebra.Matrix]
- Matrix.trace_diagonal [Mathlib.LinearAlgebra.Matrix.Trace]
- Nat.cast_pow [Mathlib.Data.Nat.Cast.Basic]
- The other Mathlib names in the file are those of RBM2D's source (compiled unchanged here: Mathlib `v4.34.0` as in `lake-manifest.json`).
- Absent in RBM3D (`Unknown identifier` at the first compile of the file): `Gauss.norm_green_le`, `Gsig_conjTranspose`, `Eblk_conjTranspose`, `gloopProd_cons`, `gloopProd_nil` (private copies or merged replacements used instead).

## (d) Open issues and paper-delta candidates
- `T2033a`: the numbers (5.2), (5.114)-(5.118), (6.4), Lemma 6.1 are the d = 2 paper's; `grep -n "(5\.11[4-8])\|(5\.2)\|(6\.4)" paper/tex/*.tex` finds only `3_5:1841` ("Following the argument for equation (5.118) in \cite{YY_25}"), whose output is `eq:boundtwochains` (`3_5:1842-1850`: block sum `≤ g²W^d Ξ Ξ`). Lean has the loop-level forms (`norm_gloop_symIdx_split_le`, `loopMax_two_mul_add_le`, `loopXi_le`) for one deterministic `(H, z)`; the passage to `eq:boundtwochains` (powers of `A` as in `loopXi_le`) is the consumer's and is not checked here. No Lean statement of `eq:boundtwochains` itself is in this ticket.
- `T2033b`: `loopMax`/`loopXi` are for fixed deterministic `H`, `z`, maximum over all signs and labels; the paper's `Ξ^{(L)}_{v,m}` is random (loops of `H_v`, supremum over `v ∈ [s,u]`, `≺`). `loopXi_le` takes `A ≥ 0` free (paper: `A = g² W^d`, `3_5:1846`).
- `T2033c`: short name `loopMax` is shared by `RBM.Ind.loopMax` and `RBM.Gauss.loopMax`; renaming one (name only) is the dispatcher's decision.
- `norm_Gsig_le` keeps RBM2D's `[Nonempty n]` (unused here), so that its statement stays RBM2D's.
- Not done: the root import (hub, at merge); no registry line; no open obstruction; the four targets build and carry the instances above.
