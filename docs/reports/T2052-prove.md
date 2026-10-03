Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 15:06:22 UTC 2026

Source: RBM2D `Green/LDEQuadT.lean` at `c9a24cf` (1209 lines; `mom_le_momVpow` at :995; bare line numbers `:NNN` in the table are lines of this RBM2D file). Merged base: `RBM3D/Green/LDEQuadMom.lean` (`mom_succ_le` :646, `Vq` :592, `momTpow` :625, `Vq_eq_ldeQuadRHS` :761), `RBM3D/Green/LDEQuad.lean` (`young_pow` :118, `GaussIBP` :302, `RowChaos` :338, `Tq` :407).

### (i) Exponent table

Notation: `C : RowChaos sz κ`, `p = q+1`, `Q = C.chaos`, `T = C.Tq = Σ_k σ_k(‖U_k‖²+‖V_k‖²)`, `Vq = Σ_{k,l} σ_k‖B_kl‖²σ_l`, `mom p = E‖Q‖^{2p}`, `momTpow p = E T^p`, `momVpow p = E Vq^p`.

| Item | Value | Constraint it must satisfy | Slack |
|---|---|---|---|
| Target `mom_le_momVpow` (:995) | `mom (q+1) ≤ ((2q+1)(4q+2))^{q+1} · momVpow (q+1)`, hypotheses `hG : GaussIBP sz`, `q : ℕ` | composition of the two rows below | none beyond product of constants |
| `mom_succ_le` (merged) | `mom (q+1) ≤ (2q+1)^{q+1} · momTpow (q+1)` | uses `hG`; exponent `2q+1 = K₁` | merged, not re-proved |
| `momTpow_le` (:914) | `momTpow (q+1) ≤ (4q+2)^{q+1} · momVpow (q+1)` | closes from the recursion row below | constant is exact in the Young closure (no loss) |
| `momTpow_succ_le` (:849) | `momTpow (q+1) ≤ (4q+2) · E[Vq T^q]` | diag term `2·E[Vq T^q]` + cross term `|·| ≤ 4q·E[Vq T^q]` (`norm_crossT_le`, :726) | at `q = 0` the cross term is 0, so `E T = 2 E Vq` is an equality case |
| Young step, `K = 4q+2` | `(q+1)(Vq K) T^q ≤ (Vq K)^{q+1} + q T^{q+1}` (`young_pow`, a := Vq·K, b := T) | `K > 0`, `Vq, T ≥ 0` | `1 - q/(q+1) = 1/(q+1) > 0` is the coefficient left on `E T^{q+1}`; subtracting it needs `E T^{q+1} < ∞` (`integrable_Tq_pow`, from `hG`) |
| Constant `c(p) = ((2p-1)(4p-2))^p` | p=1: 2; p=2: 324; p=3: 125000; p=4: 92236816 | = `(2p-1)^p · (4p-2)^p` (`mul_pow`) | identity |
| Chaos moment identity at `p=1` | `E‖Q‖² = E Vq` (not in Lean here; MC below) | — | target gives factor 2 slack |
| `Vq_eq_ldeQuadRHS` (merged, :761) | `Vq ω = t² · ldeQuadRHS S G i` | hyps `hsg: sg k = t S_{ik}`, `hsg': sg k = t S_{ki}` (inherited from RBM2D, T2044 (d)); factor `t²` | not used by this ticket's target; downstream S1-19 |
| Dimension / scale exponents | none: no exponent of `W`, `L`, `N`, `d`, no `Z2`, `zdist2`, `scaleM`, `ellT`, `Meta` in the file | portmap P.7 row 52 (T2015-portmap.md:62) has `-` in the d=2 column; script below | dimension-free (class a) |
| `GaussIBP sz` | `Prop` structure (`stein`, `polyInt`) on the product measure | structural in the sense of DECISIONS §19/§20; kept as hypothesis `hG`, discharged only by S1-19 | n/a |

Dimension-token check (script output):
```
$ git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Green/LDEQuadT.lean | grep -n "Z2\|W \^ 2\|zdist2\|scaleM\|ellT\|tailT\|ellStar\|Meta\|ellz\|(W \* L)\|Idx L\|size"
1013:there, so a fresh copy with the prefix `chkT`): the size sequence `W_n = L_n = n + 3`, slice
1021:/-- The private size sequence `L n = W n = n + 3`. -/
$ grep -n "unused" docs/reports/T2015-portmap.md | grep -i "LDEQuadT"; echo rc=$?
rc=1
```
The only hits are the word "size" in the compile-check section (:1010-1209); no d = 2 token in :56-1010. Portmap row 52 carries no "unused" marker for this file, so no declaration is dropped on the portmap's authority; the check section (`chkT*`, private) is re-instantiated at `sz0` (d = 3), see (ii).

Public declarations of the source (all in namespace `RBM.Green.RowChaos`): `wirtVal`, `wirtVal_add/_smul/_sum/_mul_right`, `integral_conj_h_mul_gen`, `TA`, `TB`, `tameTA/TB`, `hasDerivAt_Tq_true/false`, `wirtVal_term`, `wirtVal_TA_TB`, `Wt`, `tameWt`, `Tq_eq_sum_conj_h_mul`, `wirtVal_termW/_Wt`, `WA/WB`, `tameWA/WB`, `hasDerivAt_Wt_true/false`, `wirtVal_WA_WB`, `Zt/ZA/ZB`, `tameZt/ZA/ZB`, `Tq_pow_succ_eq_sum`, `hasDerivAt_Zt_true/false`, `wirtVal_ZA_ZB`, `integral_Tq_pow_succ`, `sum_sg_mul_normSq`, `sum_w_diag`, `weighted_cauchy`, `nat_mul_pow_pred`, `Arow` (+`_nonneg`), `norm_Wt_le`, `norm_sum_UV_le`, `sum_sg_normSq_U_le/V_le`, `sq_Arow_le`, `crossT`, `Vq_nonneg`, `sum_w_wirtVal_ZA_ZB`, `norm_crossT_le`, `tameCrossT`, `tameWirt`, `integrable_Vq_mul_Tq_pow`, `integrable_Vq_pow`, `momVpow` (+`_nonneg`), `momTpow_succ_le`, `momTpow_le`, `mom_le_momVpow`. (Which of them stage 1b may drop as unused is not decided here. The merged LDEQuad/LDEQuadMom already hold `Tq`, `Vq`, `momTpow`, `integrable_Tq_pow`, `momTpow_nonneg`, `Tq_complex`, `Vq_complex`, `tame_ofReal_Vq`; those must not be copied, ST1-COMMON item 11.)

### (ii) Concrete nondegenerate instances

**(1) The Lean instance (ST1-COMMON item 7).** `sz0` slice `n = 0` (RBM3D/Defs/Sizes.lean:260-267): `d = 3`, `L = 4`, `W = 32`, `lam = 1/64`, `N = (WL)^3 = 2097152`; `κ = {k : Fin 3 // k ≠ 0}` (2 elements), `eps = 1`, `r = 1`, `B = [[2,1],[0,3]]` constant (`Ifree = ∅`, `Bbd = 3`), the merged check data of `LDEQuadMom` :804-962. `σ_1 = W^{-3}(1+6g²)^{-1} = 1/32816`, `σ_2 = σ_1 g² = 1/134414336`, both > 0; `hG : GaussIBP sz0` stays a hypothesis (S1-19). Every other hypothesis is discharged.
```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2052/inst.py
sigma = [Fraction(1, 32816), Fraction(1, 134414336)] = [3.047294002925402e-05, 7.439682624329595e-09]
Vq = 9587567/2581030531760128 = 3.7146275032483946e-09 > 0: True
p=1: E|Q|^2p=3.6486e-09  <= c(p) Vq^p = 7.4293e-09 (c=2);  E T^p=7.2627e-09 <= (4p-2)^p Vq^p = 7.4293e-09
p=2: E|Q|^2p=1.2710e-16  <= c(p) Vq^p = 4.4707e-15 (c=324);  E T^p=1.0693e-16 <= (4p-2)^p Vq^p = 4.9674e-16
p=3: E|Q|^2p=1.3893e-23  <= c(p) Vq^p = 6.4070e-21 (c=125000);  E T^p=2.4012e-24 <= (4p-2)^p Vq^p = 5.1256e-23
```

**(2) Ticket's Monte Carlo at `d = 3, W = 2, L = 3`** (`N = 216`; Sizes needs only `3 ≤ L`, `0 < W`). Hermitian complex Gaussian ensemble with `E|H_xy|² = t S_xy`, `S_xy ∝ 2^{-|x-y|_∞}` (periodic on `Z_6^3`, rows sum to 1), `t = 0.5`, `ξ = 0.3+0.5i`, row `i = 0`, `h_k = H_{0k}`, `B = G^{(0)}` (`greenMinor`, resampled each sample, independent of the row), `σ_k = t S_{0k}`, `r = √t`, 10⁴ samples. Also checks `Vq = t² ldeQuadRHS` and the minor formula.
```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2052/mc.py
d=3 W=2 L=3 N=216 t=0.5 xi=(0.3+0.5j) samples=10000 sum sigma=0.4900 
max |minor formula - inverse of minor| = 2.53e-15;  max |Vq - t^2 ldeQuadRHS| = 0.00e+00
p | E|Q|^2p | (2p-1)^p E T^p | E T^p | (4p-2)^p E Vq^p | E Vq^p | c(p)=((2p-1)(4p-2))^p | c(p) E Vq^p | ok1 ok2 ok3
1 | 2.4974e-03 | 4.9737e-03 | 4.9737e-03 | 4.9735e-03 | 2.4868e-03 | 2 | 4.9735e-03 | True False True
2 | 1.4095e-05 | 2.2500e-04 | 2.5000e-05 | 2.2263e-04 | 6.1842e-06 | 324 | 2.0037e-03 | True True True
3 | 1.3413e-07 | 1.5873e-05 | 1.2698e-07 | 1.5380e-05 | 1.5380e-08 | 125000 | 1.9225e-03 | True True True
4 | 1.8555e-09 | 1.5648e-06 | 6.5175e-10 | 1.4694e-06 | 3.8250e-11 | 92236816 | 3.5280e-03 | True True True
p=1 identity 2E|Q|^2 = E T:  4.9948e-03 vs 4.9737e-03
p=1 (q=0, cross term 0, equality case of momTpow_le): mean(T-2Vq) = 1.959e-07 +- 5.111e-06 (1 s.e.); so ok2 False at p=1 is within MC noise
```
Reading: columns are `E|Q|^{2p}`, `(2p-1)^p E T^p` (merged `mom_succ_le`), `E T^p`, `(4p-2)^p E Vq^p` (`momTpow_le`), `E Vq^p`, `c(p)`, `c(p) E Vq^p` (target). The three inequalities hold for p = 1..4 except `ok2` at `p = 1`, which is the equality case `E T = 2 E Vq` (mean of `T-2Vq` is `1.96e-7 ± 5.1e-6`, 0.04 s.e.). Slack of the target at p = 3: `1.34e-7` vs `1.92e-3`.

### Verdict

- `mom_le_momVpow` (:995) and its chain `momTpow_succ_le`, `momTpow_le`: **PASS**. The exponents close exactly (`K = 4q+2`; coefficient `1/(q+1) > 0` left after Young), all hypotheses hold at the instances above, the file is dimension-free (no d = 2 token to replace), and the merged `mom_succ_le` supplies the first factor with the same `hG`.

## (a′) Preflight corrections — Sat Oct  3 15:10:41 UTC 2026

- Row 'GaussIBP sz' of the table calls the predicate structural. RBM3D/Test/Axioms.lean:88-90 lists `RBM.Green.GaussIBP` in `owedProps` (proved by S1-19). Verdict unchanged; no registry line is needed either way.

## (b) Script output — Sat Oct  3 15:10:18 UTC 2026

Branch t/T2052, commit 5842329, file RBM3D/Green/LDEQuadT.lean (1200 lines). Sole writable file touched: `git diff --stat main...t/T2052` below.
```
$ git diff --stat main...t/T2052
 RBM3D/Green/LDEQuadT.lean | 1200 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1200 insertions(+)

$ lake build RBM3D.Green.LDEQuadT 2>&1 | tail -3

Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3247 jobs).

$ lake build 2>&1 | tail -2   (full library, root #assert_rbm_axioms)
non-vacuity certificates: 4 of 48 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (3774 jobs).

$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Green/LDEQuadT.lean; echo rc=$?
rc=1
```

Axioms of the targets (script: `#print axioms` on every one of the 61 public declarations: all 61 print exactly `[propext, Classical.choice, Quot.sound]`):
```
'RBM.Green.RowChaos.norm_crossT_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.RowChaos.momTpow_succ_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.RowChaos.momTpow_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.RowChaos.mom_le_momVpow' depends on axioms: [propext, Classical.choice, Quot.sound]
count of public decls with standard axioms only:
61
```

Registry pre-check (ST1-COMMON item 8): scratch `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2052/precheck.lean` = `import RBM3D`, `import RBM3D.Green.LDEQuadT`, `#assert_rbm_axioms`; `lake env lean`:
```
exit=0
axiom audit: 1909 theorems, 828 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
  RBM.Green.GaussIBP: 17 [no certificate]
```
No new hypothesis predicate is introduced: the only premise is `RBM.Green.GaussIBP sz`, already registered in `owedProps` (RBM3D/Test/Axioms.lean:88-90; proved by S1-19). Hence RBM3D/Test/Axioms.lean is not modified.

Targets (extracted by script from the file):
```
theorem mom_le_momVpow (hG : GaussIBP sz) (q : ℕ) :
    C.mom (q + 1)
      ≤ ((2 * (q : ℝ) + 1) * (4 * (q : ℝ) + 2)) ^ (q + 1) * C.momVpow (q + 1) := by
theorem momTpow_le (hG : GaussIBP sz) (q : ℕ) :
    C.momTpow (q + 1) ≤ (4 * (q : ℝ) + 2) ^ (q + 1) * C.momVpow (q + 1) := by
theorem momTpow_succ_le (hG : GaussIBP sz) (q : ℕ) :
    C.momTpow (q + 1) ≤ (4 * (q : ℝ) + 2) * ∫ ω, C.Vq ω * C.Tq ω ^ q ∂(Sizes.seqP sz) := by
```

Statement diff to the source (RBM2D `c9a24cf:RBM2D/Green/LDEQuadT.lean` lines 56-1008 after renaming R1 `d : Sizes` -> `sz : Sizes d`, `Sizes.SeqΩ d` -> `Sizes.SeqΩ sz`, `Tame d`, `GaussIBP d`, `RowChaos d κ`, `Tame.const (d := d)` -> `(sz := sz)`), applied by perl, versus the new body (the three residual diffs are `show` -> `change` and one line wrap, for linters; no statement differs):
```
278c278
<     show (starRingEnd ℂ) (∑ m, C.h ω m * C.B ω m k) = _
---
>     change (starRingEnd ℂ) (∑ m, C.h ω m * C.B ω m k) = _
707c707
<           show C.w l * _ = 2 * C.r ^ 2 * C.w l * _
---
>           change C.w l * _ = 2 * C.r ^ 2 * C.w l * _
803c803,804
<       Integrable (fun ω : Sizes.SeqΩ sz => ((2 * C.Vq ω * C.Tq ω ^ q : ℝ) : ℂ)) (Sizes.seqP sz) := by
---
>       Integrable (fun ω : Sizes.SeqΩ sz => ((2 * C.Vq ω * C.Tq ω ^ q : ℝ) : ℂ))
>         (Sizes.seqP sz) := by
$ diff of public declaration-name lists (source vs new): rc=0
```

Name-clash grep: each of the 61 public names (all in namespace `RBM.Green.RowChaos`) searched with `grep -rlw -- NAME RBM3D --include='*.lean'` excluding LDEQuadT.lean:
```
Zt : RBM3D/Kernel/PropT.lean
$ grep -nw Zt RBM3D/Kernel/PropT.lean
148:  set Zt := ((L : ℝ) ^ (k + 2) * w)⁻¹ with hZt
151:  change ∑ c, (Au * P (a - c) + Zu) * E (a - c) * ((At * P (c - b) + Zt) * E (c - b))
```
The single hit is a local `set Zt := ...` inside a proof (PropT.lean:148), not a declaration: no clash.

Port provenance: RBM2D `RBM2D/Green/LDEQuadT.lean` lines 56-1008 at `c9a24cf`; RBM2D HEAD now `9e0f275`:
```
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Green/LDEQuadT.lean
 RBM2D/Green/LDEQuadT.lean | 213 ++--------------------------------------------
 1 file changed, 5 insertions(+), 208 deletions(-)
```

Compiled nonempty instances (file tail, section `Checks`; data `SizesInst.sz0` slice 0: d = 3, L = 4, W = 32, lam = 1/64; `kappa` = {k : Fin 3 // k != 0} (2 elements), `B = [[2,1],[0,3]]`, `sigma_k = S_{0k} > 0` proved by `chkT_sg_pos`, `Vq > 0` by `chkT_Vq_pos`; `GaussIBP sz0` is the only hypothesis left, an owed premise (`owedProps`) discharged by S1-19):
```
section Instances

variable (hG : GaussIBP sz0)
include hG

/-- **Instance of `mom_le_momVpow`** (the target) at `q = 0, 1, 2` (`p = 1, 2, 3`), on the
nondegenerate chaos with `Vq > 0` (`chkT_Vq_pos`): `GaussIBP sz0` a hypothesis (S1-19), every
other hypothesis discharged. -/
example :
    chkTChaos.mom 1 ≤ ((2 * ((0 : ℕ) : ℝ) + 1) * (4 * ((0 : ℕ) : ℝ) + 2)) ^ (0 + 1) *
        chkTChaos.momVpow (0 + 1) ∧
    chkTChaos.mom 2 ≤ ((2 * ((1 : ℕ) : ℝ) + 1) * (4 * ((1 : ℕ) : ℝ) + 2)) ^ (1 + 1) *
        chkTChaos.momVpow (1 + 1) ∧
    chkTChaos.mom 3 ≤ ((2 * ((2 : ℕ) : ℝ) + 1) * (4 * ((2 : ℕ) : ℝ) + 2)) ^ (2 + 1) *
        chkTChaos.momVpow (2 + 1) :=
  ⟨chkTChaos.mom_le_momVpow hG 0, chkTChaos.mom_le_momVpow hG 1, chkTChaos.mom_le_momVpow hG 2⟩

/-- **Instance of `momTpow_le`** at `q = 0, 1`. -/
example :
    chkTChaos.momTpow (0 + 1)
      ≤ (4 * ((0 : ℕ) : ℝ) + 2) ^ (0 + 1) * chkTChaos.momVpow (0 + 1) ∧
    chkTChaos.momTpow (1 + 1)
      ≤ (4 * ((1 : ℕ) : ℝ) + 2) ^ (1 + 1) * chkTChaos.momVpow (1 + 1) :=
  ⟨chkTChaos.momTpow_le hG 0, chkTChaos.momTpow_le hG 1⟩

/-- **Instance of `momTpow_succ_le`** at `q = 1`. -/
example :
    chkTChaos.momTpow (1 + 1)
      ≤ (4 * ((1 : ℕ) : ℝ) + 2) * ∫ ω, chkTChaos.Vq ω * chkTChaos.Tq ω ^ 1
          ∂(Sizes.seqP sz0) :=
  chkTChaos.momTpow_succ_le hG 1

end Instances

/-- **Instance of `norm_crossT_le`** at `q = 0`: the cross term vanishes. -/
example (ω : Sizes.SeqΩ sz0) :
    ‖chkTChaos.crossT 0 ω‖ ≤ 4 * ((0 : ℕ) : ℝ) * chkTChaos.Vq ω * chkTChaos.Tq ω ^ 0 :=
  chkTChaos.norm_crossT_le 0 ω

end Checks
```

Dimension-token accounting (rule R2/R3 of ST1-COMMON item 2): `grep -n "Z2\|W \^ 2\|zdist2\|scaleM\|ellT\|tailT\|ellStar\|Meta\|ellz\|(W \* L)\|Idx L" RBM3D/Green/LDEQuadT.lean` outside the Checks section:
```
count of hits before Checks: 0
```

Narrative.
- The file is a direct port of RBM2D LDEQuadT (c9a24cf, :56-1008): only the rule-R1 renaming was needed; the source's imports (`RBM2D.Green.LDEQuadMom`) become `RBM3D.Green.LDEQuadMom`. The file is dimension-free (class a): zero d = 2 tokens before the Checks section, as the grep above shows.
- `Tq`, `Vq`, `momTpow`, `integrable_Tq_pow`, `momTpow_nonneg`, `Tq_complex`, `Vq_complex`, `tame_ofReal_Vq` are the merged ones in LDEQuad/LDEQuadMom and are not copied (ST1-COMMON item 11); the name-list diff shows the file defines exactly the source's public declarations (none dropped; the portmap marks none unused).
- Nothing in the file required a change beyond renaming; the proof text is the source's, byte for byte, except three linter-motivated edits listed in the diff above.
- The Checks section re-instantiates the source's `chkT` checks at `sz0` (d = 3) using the data of the merged LDEQuadMom checks (copied with prefix `chkT`, as those are private there). The source's two-index `W = L = n+3` size sequence is replaced by `sz0`; the source's `chkT_gvar` computation is replaced by `chkT_svarF_one/_two`, `chkT_sg`.
- Instances apply `mom_le_momVpow` at q = 0,1,2, `momTpow_le` at q = 0,1, `momTpow_succ_le` at q = 1, `norm_crossT_le` at q = 0; only `hG : GaussIBP sz0` is a hypothesis of the examples.
- Section (a) numbers are not edited. Preflight (ii)(1) states sigma_1 = 1/32816 and sigma_2 = sigma_1 g^2 with `Bbd = 3`; the Lean instance uses the same data (`chkT_svarF_one/_two`).

## (c) Verified Mathlib names used (all by compilation of the file)
- `Finset.single_le_sum`, `Finset.notMem_empty`, `Finset.sum_nonneg`, `MeasureTheory.integral_nonneg`, `Complex.ofReal_sum`: used by the new check lemmas and the ported body; the file builds. No name was invented; none verified absent.

## (d) Open issues and paper-delta candidates
- None new. The inherited factor `t^2` / hypothesis `hsg'` of `Vq_eq_ldeQuadRHS` (T2044 (d)) concerns LDEQuadMom, not this file; `mom_le_momVpow` is stated for `Vq` itself.
- `GaussIBP sz` stays a hypothesis of every integrating declaration (S1-19 owes it). The target is a conditional result for an abstract `RowChaos`, not the paper's resolvent-entry LDE (S1-19 uses it).
- No paper-delta candidate (T2052a ...): the paper does not state this file.
