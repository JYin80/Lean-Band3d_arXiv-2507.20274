Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 10:26:39 UTC 2026

Targets (mathematics only): for the row chaos `Q = Σ_{k,l} h_k B_kl conj(h_l) − Σ_k σ_k B_kk`, `h_k = r(a_k + ε_k i b_k)`, `σ_k = 2 r² w_k`, `B` bounded and independent of the row coordinates:
(T1) the moment bound `E|Q|^{2p} ≤ (2p−1)^p E[T^p]`, `p ≥ 1` (RBM2D `c9a24cf` `Green/LDEQuadMom` `mom_succ_le`), with integrability `integrable_norm_pow` (:509) from `GaussIBP` (Stein + polynomial moments); (T2) `Vq_eq_ldeQuadRHS` (:765): `Vq = Σ_{k,l} σ_k |B_kl|² σ_l = t² · ldeQuadRHS` when `σ_k = t S_ik = t S_ki`, `B_kl = G^{(i)}_kl`. Both are dimension-free: `d` enters only through the model `Sizes d` (variances `gvar`), and the source lines 1–795 (before `section Checks`, line 796) contain no `Z2`, `Idx L W`, `W^2`, `svar` token; the `^ 2` tokens are the exponent in `σ = 2r²w`.

### (i) Exponent table

| Constant / threshold | Value | Constraint | Slack |
|---|---|---|---|
| Hanson–Wright constant at `p = q+1` | `(2p−1)^p` = 1, 9, 125, 2401 for p = 1..4 | recursion `2E|Q|^{2(q+1)} ≤ (2q+1)E[T|Q|^{2q}]` closed by Young with `K = 2q+1 > 0` | sharp coefficient is `K^p/(q+2)`; stated one loses factor `q+2` (2, 3, 4, 5 for p = 1..4; table below) |
| Cross-term bound `‖R‖ ≤ T/2` | 1/2 | `|σ_k U_k V_k| ≤ σ_k(|U_k|²+|V_k|²)/2` | holds on all 10⁴ MC samples (script 1); equality only if `|U_k| = |V_k|` |
| Recursion constant | `2q+1` | `2q‖X‖ ≤ q·E[T|Q|^{2q}]` via `‖X‖ ≤ momT(q)/2`, plus `(q+1)E[T|Q|^{2q}]` | MC q=1: `2E|Q|⁴ = 1.816e-4 ≤ 3E[T|Q|²] = 2.337e-4`; q=0 is an identity (`2E|Q|² = E[T]`, ratio 1.0001) |
| Young coefficients (`young_pow q`: `(q+1)ab^q ≤ a^{q+1} + q b^{q+1}`) | `A = K^q/(q+1)`, `B = q/((q+1)K)` | `a = TK`, `b = |Q|²`, `a,b ≥ 0`; need `K·B = q/(q+1) < 2` to absorb | `2 − q/(q+1) ≥ 1` for all q, so dropping to `E|Q|^{2p} ≤ K^p E[T^p]` is valid with room (table below) |
| `E[T]` vs `Vq` (NOT in the file) | `E[T] = 2E[Vq]`, `E|Q|² = E[Vq]` | needs row isometry; not ported | MC ratio `E[T]/(2Vq) = 0.9984`, `E|Q|²/Vq = 0.9984` |
| `Vq` vs `ldeQuadRHS` factor | `t²` | `σ_k = t S_ik`, `σ_k = t S_ki` (both hypotheses) | exact: rel. diff `1.7e-15` (script 1) |
| `σ_k` in the instance | `σ = 2r²w = t·S_xy`, `S_xy = W^{-d}(1+2dg²)^{-1}` for same or neighbouring block | `w ≥ 0`; `σ_k > 0` for a nondegenerate chaos | d=3, W=2, g=1: `S = 1/56`, `w = 1/112`, 55 nonzero `σ_k` among 215 (`python3 cnt.py` prints `nonzero sigma_k (k != 0): 55 of 215`); `σ = 1/56` in script 2 |
| Dimension of the model | `N = (WL)^d` = 216 at d=3, W=2, L=3 | `L ≥ 3`, `W ≥ 1` (`Sizes d`); `lam` unconstrained by `Sizes` | row sums of `S` equal 1 (script 1) |
| `B` bound `Bbd` | 1.19 (script 1: `max|G^{(i)}| `at `z = 0.3+0.5i`, bound ≤ 1/η = 2) | continuity, `B_free` (`Ifree` has no row coordinate) | script 2 uses constant `B = [[2,1],[0,3]]`, `Bbd = 3`, `Ifree = ∅` |

Constants per `q` (script 3): Young coefficients, sharp coefficient and stated `(2p−1)^p`:
```
$ python3 scratchpad/T2044/exps.py
q=0 p=1 K=1  Young coeffs A=1 Bc=0  sharp coeff K^p/(q+2)=1/2  stated (2p-1)^p=1  slack factor q+2=2
q=1 p=2 K=3  Young coeffs A=3/2 Bc=1/6  sharp coeff K^p/(q+2)=3  stated (2p-1)^p=9  slack factor q+2=3
q=2 p=3 K=5  Young coeffs A=25/3 Bc=2/15  sharp coeff K^p/(q+2)=125/4  stated (2p-1)^p=125  slack factor q+2=4
q=3 p=4 K=7  Young coeffs A=343/4 Bc=3/28  sharp coeff K^p/(q+2)=2401/5  stated (2p-1)^p=2401  slack factor q+2=5
q=4 p=5 K=9  Young coeffs A=6561/5 Bc=4/45  sharp coeff K^p/(q+2)=19683/2  stated (2p-1)^p=59049  slack factor q+2=6
q=5 p=6 K=11  Young coeffs A=161051/6 Bc=5/66  sharp coeff K^p/(q+2)=1771561/7  stated (2p-1)^p=1771561  slack factor q+2=7
```

Declarations of the source at `c9a24cf` (970 lines; `grep` of `^theorem|^def|^section|^end`): `integral_chaos_mul` (96), `eps_sq_complex`, `sg_complex`, `conj_dA`, `conj_dB`, `sum_w_sq`, `sum_w_normSq`, `tameRq`, `tameTq`, `moment_recursion` (320), `mom`, `momT`, `ofReal_norm_pow`, `tame_ofReal_norm_pow`, `tame_ofReal_Tq_mul`, `ofReal_normSq`, `mom_nonneg`, `momT_nonneg`, `integral_ofReal'`, `integral_chaos_pow`, `integral_Tq_chaos_pow`, `integrable_of_tame_ofReal`, `integrable_norm_pow` (509), `integrable_Tq_mul`, `norm_integral_Rq_le`, `two_mul_mom_succ_le` (550), `Vq`, `Vq_complex`, `tame_ofReal_Vq`, `Tq_complex`, `momTpow`, `integrable_Tq_pow`, `momTpow_nonneg`, `mom_succ_le` (650), `sum_erase_eq`, `norm_chaos_sq_eq_ldeQuadLHS`, `Vq_eq_ldeQuadRHS` (765). Only the private `section Checks` (796–921, `chkM*`) and the trailing `#print axioms` lines are not part of the kept 796 lines; they use the d = 2 model (`Idx L W`, `gvar_offDiag`, `sbSupport`) and are replaced by a d = 3 instance. No public declaration is dropped.

### (ii) One concrete nondegenerate instance

`d = 3`, `W = 2`, `L = 3`, `g = lam = 1`, `N = (WL)^3 = 216`; `H = √t X`, `t = 0.5`, `X` Hermitian Gaussian with `E|X_xy|² = S_xy`; `z = 0.3 + 0.5i`; row `i = 0`; `B = G^{(i)}` (215×215, one fixed sample, independent of row `i`); `h_k = r(a_k + i b_k)`, `r = √t`, `a_k, b_k ~ N(0, S_ik/2)`; 10⁴ samples of the row. Every hypothesis holds at once: `σ_k = tS_ik = tS_ki` (S symmetric), `B_kl = greenMinor G i k l`, `B` bounded and row-free, `w_k = S_ik/2 ≥ 0`, `co` injective (distinct pairs `(k, b)`).

Script 1 (`scratchpad/T2044/mc.py`; `python3 mc.py`, numpy 2.0.2, seed 20261003):
```
N = 216  rowsum range: 0.9999999999999998 1.0  S symmetric: True  offdiag S_ik values: [0.0, 0.0178571429]
greenMinor == inverse of minor: True  max|B| = 1.1914206656131912
hsg' (sigma_k = t S_ki): True
Vq = 0.006130074098728419  t^2 * ldeQuadRHS = 0.006130074098728408  rel.diff = 1.697914362571878e-15
E|Q|^2 (MC) = 0.00612042 +- 7.3e-05 ; Vq = 0.00613007 ; ratio = 0.9984
E[T] (MC) = 0.0122401 +- 1.8e-05 ; 2 Vq = 0.0122601 ; ratio = 0.9984
p=2: E|Q|^4 = 9.08053e-05 +- 3.2e-06 ; 9 E[T^2] = 0.00137872 ; ok: True
recursion q=1: 2 E|Q|^4 = 0.000181611 <= 3 E[T|Q|^2] = 0.000233651 : True
recursion q=0: 2 E|Q|^2 = 0.0122408 vs E[T] = 0.0122401 (identity, ratio 1.0001)
p=3: E|Q|^6 = 2.445e-06 <= 5^3 E[T^3] = 0.000244953 : True
max sample ||R|| <= T/2 check: True
```
The closed form behind `Vq_eq_ldeQuadRHS` (`Vq = t²·ldeQuadRHS`) agrees to `1.7e-15`; the MC second moment equals `Vq` within 0.13σ (standard error 7.3e-05) (`E|Q|² = Vq` exactly for fixed `B`, hence `2E|Q|² = E[T]`); the moment bounds at `p = 1, 2, 3` hold with margins 2, 15, 100.

Small instance for the compiled example (index type `Bool`, two coordinates per index, `r = 1`, `ε = 1`, constant `B = [[2,1],[0,3]]`, `Bbd = 3`, `Ifree = ∅`; every `σ_k = S_xy = 1/56`, `w_k = 1/112` at d = 3, W = 2, L = 3, g = 1; row and columns chosen in the same or neighbouring blocks so that `σ_k > 0`), script 2 (`scratchpad/T2044/mc2.py`; `python3 mc2.py`):
```
Vq exact = 0.0044642857 (= 14/56^2 = 0.0044642857)
p=1: E|Q|^2 = 0.0044718 <= 1*E[T^1] = 0.0088668 : True
p=2: E|Q|^4 = 0.00013025 <= 9*E[T^2] = 0.0011568 : True
p=3: E|Q|^6 = 1.1052e-05 <= 125*E[T^3] = 0.00033019 : True
E|Q|^2 MC = 0.0044718 vs Vq 0.0044643 (ratio 1.0017)
```
External hypothesis: none (`GaussIBP sz` is a hypothesis `hG` of the integrating declarations, as in the source; it is the pin of S1-12 `RBM3D/Green/LDEQuad.lean:302` and holds for `Sizes.seqP sz` by Stein's identity for independent centred Gaussians, so it may stay a hypothesis of the example).

### Verdict

- T1 (`mom_succ_le`, `integrable_norm_pow`, the recursion chain): PASS. Constants `(2p−1)^p` close for all `q` (script 3); all hypotheses hold in the instance.
- T2 (`Vq_eq_ldeQuadRHS`, `norm_chaos_sq_eq_ldeQuadLHS`): PASS. Pure reindexing; identity checked numerically to `1.7e-15` including the `t²` factor and both hypotheses `σ_k = tS_ik`, `σ_k = tS_ki`.
- The port is dimension-free (no `d = 2` token in source lines 1–795); only the instance (`section Checks`) must be rewritten at `d = 3`.

## (b) Script output — Sat Oct  3 10:32:12 UTC 2026

```
$ lake build RBM3D.Green.LDEQuadMom 2>&1 | tail -2
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3246 jobs).
$ git log -1 --format=%h; git diff --stat main...t/T2044
d329c31
 RBM3D/Green/LDEQuadMom.lean | 977 ++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 977 insertions(+)
$ lake build 2>&1 | tail -1   (full library, root #assert_rbm_axioms included)
Build completed successfully (3744 jobs).
$ lake env lean scratchpad/T2044/pre.lean   (registry pre-check: import RBM3D; import RBM3D.Green.LDEQuadMom; #assert_rbm_axioms)
axiom audit: 1517 theorems, 547 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
exit code: 0
$ #print axioms of all 37 public declarations of the file (scratchpad/T2044/axioms.lean), summarised
   1 'RBM.Green.RowChaos.integral_ofReal'' depends on axioms: [propext, Classical.choice, Quot.sound]
  36 depends on axioms: [propext, Classical.choice, Quot.sound]
$ #print axioms of the targets
'RBM.Green.RowChaos.integrable_norm_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.RowChaos.two_mul_mom_succ_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.RowChaos.mom_succ_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.RowChaos.norm_chaos_sq_eq_ldeQuadLHS' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.RowChaos.Vq_eq_ldeQuadRHS' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Green/LDEQuadMom.lean | wc -l
       0
$ diff <(RBM2D c9a24cf Green/LDEQuadMom.lean lines 70-787, mechanical renames d->sz applied) <(RBM3D file, namespace..end RowChaos)
653c653
< `RBM.Green.LDEQuad` (`RBM2D/Green/EntryCore.lean`), once the row chaos is indexed by
---
> `RBM.Green.LDEQuad` (`RBM3D/Green/EntryCore.lean`), once the row chaos is indexed by
718d717
< 
$ name-clash: for each of the 37 public declarations, grep -rn in RBM3D (outside this file) for theorem|lemma|def|abbrev|structure of that name (short or RBM.Green[.RowChaos]-qualified); counts, uniq -c
  37 0
$ grep -c "^private" file; grep -nE "d = 2|Z2|W \^ 2|Idx L W|svar |scaleM|ellT|Meta" file | wc -l
15
       0
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h c9a24cf; ... diff --stat c9a24cf HEAD -- RBM2D/Green/LDEQuadMom.lean
c9a24cf
 RBM2D/Green/LDEQuadMom.lean | 214 ++++----------------------------------------
 1 file changed, 15 insertions(+), 199 deletions(-)
```

### Target statements (extracted by script from the file)
```lean
theorem integrable_norm_pow (q : ℕ) :
    Integrable (fun ω => ‖C.chaos ω‖ ^ (2 * q)) (Sizes.seqP sz) :=
theorem mom_succ_le (q : ℕ) :
    C.mom (q + 1) ≤ (2 * (q : ℝ) + 1) ^ (q + 1) * C.momTpow (q + 1) := by
theorem two_mul_mom_succ_le (q : ℕ) :
    2 * C.mom (q + 1) ≤ (2 * (q : ℝ) + 1) * C.momT q := by
theorem Vq_eq_ldeQuadRHS (C : RowChaos sz {k : n // k ≠ i}) (ω : Sizes.SeqΩ sz)
    (G : Matrix n n ℂ) (S : n → n → ℝ) (t : ℝ)
    (hB : ∀ k l : {k : n // k ≠ i}, C.B ω k l = greenMinor G i k.1 l.1)
    (hsg : ∀ k : {k : n // k ≠ i}, C.sg k = t * S i k.1)
    (hsg' : ∀ k : {k : n // k ≠ i}, C.sg k = t * S k.1 i) :
    C.Vq ω = t ^ 2 * ldeQuadRHS S G i := by
theorem norm_chaos_sq_eq_ldeQuadLHS (C : RowChaos sz {k : n // k ≠ i}) (ω : Sizes.SeqΩ sz)
    (H G : Matrix n n ℂ) (S : n → n → ℝ) (t : ℝ)
    (hh : ∀ k : {k : n // k ≠ i}, C.h ω k = H i k.1)
    (hhc : ∀ k : {k : n // k ≠ i}, (starRingEnd ℂ) (C.h ω k) = H k.1 i)
    (hB : ∀ k l : {k : n // k ≠ i}, C.B ω k l = greenMinor G i k.1 l.1)
    (hsg : ∀ k : {k : n // k ≠ i}, C.sg k = t * S i k.1) :
    ‖C.chaos ω‖ ^ 2 = ldeQuadLHS H G S t i := by
```

### Compiled nonempty instances (from the file; data: `sz0` at `d = 3` slice 0 (`L = 4`, `W = 32`), `n = Fin 3`, `i = 0`, `κ = {k // k ≠ 0}` (2 elements), `t = 1`, `G = diag(1, [[2,1],[0,3]])`)
The chaos is defined at lines 830-844 and `chkM_sg_pos` (line 900, compiled) shows `σ_k > 0` for both columns (`S_xy = (32^3)⁻¹(1+6g²)⁻¹`, `(32^3)⁻¹g²(1+6g²)⁻¹`, `g = 1/64`, via `chkM_svarF_one`, `chkM_svarF_two`). `GaussIBP sz0` (S1-19 pin) stays the hypothesis `hG`; every other hypothesis is discharged.
```lean
section Instances
variable (hG : GaussIBP sz0)
include hG
/-- **Instance of `integrable_norm_pow`** (`GaussIBP sz0` a hypothesis, S1-19). -/
example (q : ℕ) : Integrable (fun ω => ‖chkMChaos.chaos ω‖ ^ (2 * q)) (Sizes.seqP sz0) :=
  chkMChaos.integrable_norm_pow hG q
/-- **Instance of `mom_succ_le`** at `p = 1, 2` (`q = 0, 1`): `E|Q|² ≤ 1 · E[T]` and
`E|Q|⁴ ≤ 9 · E[T²]`. -/
example : chkMChaos.mom 1 ≤ 1 * chkMChaos.momTpow 1 ∧ chkMChaos.mom 2 ≤ 9 * chkMChaos.momTpow 2 := by
  have h1 := chkMChaos.mom_succ_le hG 0
  have h2 := chkMChaos.mom_succ_le hG 1
  norm_num at h1 h2
  exact ⟨by simpa using h1, h2⟩
/-- **Instance of `two_mul_mom_succ_le`** at `q = 0` and `q = 1`. -/
example :
    2 * chkMChaos.mom 1 ≤ (2 * ((0 : ℕ) : ℝ) + 1) * chkMChaos.momT 0 ∧
      2 * chkMChaos.mom 2 ≤ (2 * ((1 : ℕ) : ℝ) + 1) * chkMChaos.momT 1 :=
  ⟨chkMChaos.two_mul_mom_succ_le hG 0, chkMChaos.two_mul_mom_succ_le hG 1⟩
/-- **Instance of `integral_chaos_mul`** with `F = 1`, `FA = FB = 0`. -/
example :
    2 * ∫ ω, chkMChaos.chaos ω * (fun _ => (1 : ℂ)) ω ∂(Sizes.seqP sz0)
      = ∑ k, (chkMChaos.w k : ℂ) * ∫ ω, (chkMChaos.dA ω k * (fun _ _ => (0 : ℂ)) k ω
          + chkMChaos.dB ω k * (fun _ _ => (0 : ℂ)) k ω) ∂(Sizes.seqP sz0) :=
  chkMChaos.integral_chaos_mul hG (Tame.const 1) (fun _ => Tame.const 0) (fun _ => Tame.const 0)
    (fun _ _ => hasDerivAt_const _ _) (fun _ _ => hasDerivAt_const _ _)
/-- **Instance of `moment_recursion`** at `q = 0`. -/
example :
    2 * ∫ ω, chkMChaos.chaos ω ^ (0 + 1) * (starRingEnd ℂ) (chkMChaos.chaos ω) ^ (0 + 1)
        ∂(Sizes.seqP sz0)
      = 2 * ((0 : ℕ) : ℂ) * ∫ ω, chkMChaos.Rq ω * (chkMChaos.chaos ω ^ (0 - 1)
          * (starRingEnd ℂ) (chkMChaos.chaos ω) ^ (0 + 1)) ∂(Sizes.seqP sz0)
        + (((0 : ℕ) : ℕ) + 1 : ℂ) * ∫ ω, ((chkMChaos.Tq ω : ℝ) : ℂ) * (chkMChaos.chaos ω ^ 0
          * (starRingEnd ℂ) (chkMChaos.chaos ω) ^ 0) ∂(Sizes.seqP sz0) :=
  chkMChaos.moment_recursion hG 0
end Instances
/-- **Instance of `Vq_eq_ldeQuadRHS`** at the private chaos, `G = diag(1, [[2,1],[0,3]])`,
`t = 1` and the lattice variance profile `S = chkMS` (every hypothesis discharged). -/
example (ω : Sizes.SeqΩ sz0) :
    chkMChaos.Vq ω = 1 ^ 2 * ldeQuadRHS chkMS chkMG (0 : Fin 3) :=
  RowChaos.Vq_eq_ldeQuadRHS (i := 0) chkMChaos ω chkMG chkMS 1
    (fun _ _ => rfl) (fun k => by rw [chkM_sg, one_mul]) (fun k => by rw [chkM_sg', one_mul])
/-- The row matrix `H_{0k} = h_k(ω)`, `H_{k0} = \bar h_k(ω)`, zero elsewhere. -/
private noncomputable def chkMH (ω : Sizes.SeqΩ sz0) : Matrix (Fin 3) (Fin 3) ℂ := fun a b =>
  if ha : a = 0 then (if hb : b = 0 then 0 else chkMChaos.h ω ⟨b, hb⟩)
  else if b = 0 then (starRingEnd ℂ) (chkMChaos.h ω ⟨a, ha⟩) else 0
/-- **Instance of `norm_chaos_sq_eq_ldeQuadLHS`** at the private chaos, the row matrix
`chkMH ω`, `G = diag(1, [[2,1],[0,3]])` and `t = 1` (every hypothesis discharged). -/
example (ω : Sizes.SeqΩ sz0) :
    ‖chkMChaos.chaos ω‖ ^ 2 = ldeQuadLHS (chkMH ω) chkMG chkMS 1 0 :=
  RowChaos.norm_chaos_sq_eq_ldeQuadLHS (i := 0) chkMChaos ω (chkMH ω) chkMG chkMS 1
    (fun k => by simp [chkMH, k.2])
    (fun k => by simp [chkMH, k.2])
    (fun _ _ => rfl) (fun k => by rw [chkM_sg, one_mul])
```

Narrative (stage 1b).
- Port: `RBM2D/Green/LDEQuadMom.lean` at `c9a24cf`, lines 1-787 (all 37 public declarations, none dropped) into `RBM3D/Green/LDEQuadMom.lean`; only rule R1 (`d : Sizes` -> `sz : Sizes d`, `Tame d`/`GaussIBP d`/`RowChaos d`/`Sizes.SeqΩ d`/`seqP d`/`seqGvar d` -> `sz`, `(d := d)` -> `(sz := sz)`) was applied; the script diff above shows the proofs and statements unchanged except one docstring path (`RBM2D/...` -> `RBM3D/...`) and the dropped trailing blank line. Header docstring rewritten for RBM3D.
- Dimension-free: the grep for `d = 2`, `Z2`, `W ^ 2`, `Idx L W`, `svar `, `scaleM`, `ellT`, `Meta` over the new file gives 0 matches; the portmap row lists no `d = 2` token; the source's `section Checks` (lines 788-921, `chkM*`, `Idx L W`, `gvar_offDiag`, `sbSupport`) is not ported and is replaced by the d = 3 section above.
- Imports `RBM3D.Green.EntryCore` (`greenMinor`, `ldeQuadLHS`, `ldeQuadRHS`) and `RBM3D.Green.LDEQuad` (`RowChaos`, `Tame`, `GaussIBP`, `young_pow`, `polyW`, `FinDep`); nothing copied from them (ST1-COMMON item 11).
- The `Tq`/`Rq`/`sg`/`w`/`chaos` definitions are those of `LDEQuad.lean`; this file adds `mom`, `momT`, `momTpow`, `Vq` (public defs, as in RBM2D).
- Axiom registry: the file introduces no new `Prop`-valued premise predicate: its integrating declarations take `GaussIBP sz` (already registered as owed in `RBM3D/Test/Axioms.lean:90`). `RBM3D/Test/Axioms.lean` is unchanged; the pre-check exited 0.
- Instance deviation from the ticket's preflight text: the compiled instance uses `sz0` (ST1-COMMON item 7), not `W = 2, L = 3`; the numeric instance at `W = 2`, `L = 3` is in section (a).
- 15 `private` declarations (instance data only). Style-linter warnings (`show`, line > 100) of the ported text are kept as in RBM2D.

## (c) Verified Mathlib names used (all appear in the compiled file)
`Finset.sum_subtype`, `MeasureTheory.integral_add`, `MeasureTheory.integral_congr_ae`, `MeasureTheory.integral_const_mul`, `_root_.integral_ofReal`, `Filter.Eventually.of_forall`, `Function.update_eq_self`, `HasDerivAt.fun_mul`, `Finset.notMem_empty`, `hasDerivAt_const`, `Complex.mul_conj`, `Complex.sq_norm`, `div_le_one`, `div_le_iff₀`: used by the build above (names inherited from the port; no new Mathlib name was introduced beyond the instance proofs, which use `fin_cases`, `decide`, `simp`, `norm_num`).

## (d) Open issues and paper-delta candidates
- No paper-delta candidate: the statements equal RBM2D's after rule R1; the factor `t²` and the second hypothesis `hsg'` of `Vq_eq_ldeQuadRHS` are inherited from the RBM2D/RBM1D text (see file docstring "Deviations").
- RBM2D `HEAD` differs from `c9a24cf` in this file (diff-stat in (b)); the port follows `c9a24cf` as ticketed.
- Downstream: S1-14 uses `RowChaos.mom_succ_le`, `Vq_eq_ldeQuadRHS`; ST-2 uses `integrable_norm_pow` (public, unchanged name).
- Root import `import RBM3D.Green.LDEQuadMom` is to be added by the hub at merge.
