Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 19:26:19 UTC 2026

Sources: ticket T2063; RBM2D `c9a24cf` `Hierarchy/WardResolvent.lean` (162 lines) and `Induction/ConArgDet.lean` (1348 lines at `c9a24cf`);
paper `paper/tex/1_2_Intro_model_result.tex:1036-1042` (`WI_calL`: `Σ_{a_n} L^{(n)} = (2i W^d η_t)^{-1}(L^{(n-1),+} − L^{(n-1),−})`) and `3_5_Loop_Hierarchy.tex:42-57` (`lem_ConArg`, `ε ≤ s ≤ t ≤ 1`, proof "exactly as [YY_25] Lemma 5.1").
Setting: `Vtx d L W = Zd d L × Fin (W^d)` (`RBM3D/Gauss/Model.lean:60`), `(E_a)_{xy} = W^{-d} 1(x=y∈[a])` (`RBM3D/Loop/GLoop.lean`, `Eblk`); `L^d` labels, `N = (WL)^d`.

### (i) Exponent table

| # | Quantity (RBM2D → d ≥ 3) | Value | Constraint it must satisfy | Slack / check |
|---|---|---|---|---|
| 1 | block weight in `E_a`, `bw`: `W⁻²` → `W^{-d}` | `(W^d)⁻¹` | block `[a]` has `W^d` sites, `tr E_a = 1` | `Σ_a E_a = W^{-d}·1` (each site in exactly one block) |
| 2 | Ward, `sum_gloop_ward_last`: `2iη Σ_b L^{(n)}_{(+,μ,−),(x,a',b)} = W^{-d}(L_{(+,μ)} − L_{(−,μ)})` | factor `W^{-d}` | = paper `WI_calL` (`1/(2iW^dη)`); case `σ_1=+, σ_n=−` only (paper also has `σ_1=−, σ_n=+`, not ported) | script: rel. err `≤ 4.6e-16`; with `W²` (d=2 factor) rel. err = 1.000 (factor `W^d/W² = 2` at `d=3, W=2`) |
| 3 | `sum_gloop_ward_last_div` denominator `2i W² Im z` → `2i W^d Im z` | needs `W ≥ 1` (`(W:ℂ)^d ≠ 0`), `Im z ≠ 0` | denominator ≠ 0 | `W^d = 8`, `Im z = 0.484` at the instance |
| 4 | row identity (6.12) `tr(E_{a0}PPᴴ) = W^{-d} Σ_{α∈Fin(W^d)} Σ_k |P_{(a0,α),k}|²`, `ward_chain_row(')`, `sum_norm_gchain_row_sq_le`: `W^{-d}Σ_α Σ_k |v_{(a0,α),k}|² ≤ (Im z)⁻¹ loopMax(2l+1)` | `W^{-d}` | row sum over `W^d` sites of the block; `‖(2iIm z)⁻¹‖ = (2 Im z)⁻¹`, two loops of length `2l+1` | constant 1 (as RBM2D); no `d`-dependence other than `W^{-d}` |
| 5 | `blockSel` `R: (Fin (W^d)) → Vtx`, `R Rᵀ = W^d E_b`, `Rᵀ R = 1_{W^d}` | `W^d` | `R Rᵀ = 1_{[b]}` = `W^d · W^{-d} 1_{[b]}` | exact identity |
| 6 | `trace_gram_blockCols_pow`: `tr A^{p+1} = (W^d)^{p+1} tr((YᴴY E_b)^{p+1})` | `(W^d)^{p+1}` | from row 5, `A = Rᵀ(YᴴY)R` | exact |
| 7 | `trace_gram_rpow_le`: `(Re tr A^p)^{1/p} ≤ W^d (Im w)⁻¹ loopMax_w(p(2k−1))^{1/p}` | `W^d` (was `W²`) | needs `2‖(2i Im w)⁻¹‖ = (Im w)⁻¹ ≤ β`; `YᴴY E_b = (2iIm w)⁻¹(Z₊−Z₋)`, `Z_±` loop products of length `2k−1`; `p ≥ 1`, `Im w > 0` | script: max_b LHS/RHS = 0.9818 (p=1), 0.9791 (p=2) at `k=1`, so ≤ 1 with slack 0.018, 0.021 |
| 8 | `sum_bw_mul`: `Σ_i bw_b(i) f(i) = W^{-d} Σ_{α∈Fin(W^d)} f(b,α)` | `W^{-d}` | `Σ_p bw_b(p) = 1` | exact |
| 9 | `wmass_gchain_mul_gchain_le`: `wmass ≤ (Im z Im w)⁻¹ loopMax_z(2l+1) loopMax_w(p(2k−1))^{1/p}` | no `W` left | `wmass = W^{-d}Σ_α[W^{-d}Σ_β|M|²] ≤ W^{-d}·(W^{-d}Σ_αΣ_k|X|²)·T`, row 4 bounds the bracket by `(Im z)⁻¹ loopMax_z`, row 7 gives `T ≤ W^d(Im w)⁻¹…`; net `W^{-d}·W^{d} = 1` | exponents of `W^d` cancel exactly, as `W^{-2}·W^2` in RBM2D; no `ℓ_t`, `η`, `N` appears |
| 10 | `loopMax_two_mul_le_tilde`: `max|L_z^{(2m)}| ≤ (m+1)(max|L_w^{(2m)}| + |z−w|² (Im z Im w)⁻¹ Σ_{l<m} max|L_z^{(2l+1)}| max|L_w^{(p(2(m−l)−1))}|^{1/p})` | `m ≥ 1`, `p ≥ 1`; constant `m+1` | `Im z, Im w > 0`; `H` Hermitian | dimension-free (no `W^d`, `ℓ_t`, `N`); script slack: RHS−LHS = 0.6046 (p=1), 0.2222 (p=2) |
| 11 | `ztTilde_arith` constants: `z̃ = √(t₂/t₁) z_{t₁}`, `C = (3/c+1) + K² + c⁻¹`, `K = (3/c+1)(2/κ)` | at `c=1/4, κ=1`: `K = 26`, `C = 693` | `0<c ≤ t₁ ≤ t₂ ≤ 1`, `|E| ≤ 2−κ`, `κ>0` (paper `ε ≤ s ≤ t ≤ 1`) | `|z_{t₂}−z̃| = 0.5470 ≤ C(1−t₁) = 519.75`; `|·|² = 0.2992 ≤ Cη² = 365.45`; `|·|²/Im z̃ = 0.2913 ≤ Cη = 503.25`; `η_{t₁} = 0.7262 ≤ Im z̃ = 1.0270 ≤ Cη = 503.25` |
| 12 | `etaT E t = (1−t)(m^{(E)}).im` (RBM2D `Path.etaT`, `Path/Scales:38`), `spectralM = mE`, `spectralZ E t = E + (1−t) m^{(E)} = zt` | `d`-free | `ztTilde_arith` uses only `etaT`, `spectralM_im = √(4−E²)/2`, `‖m^{(E)}‖ = 1` for `|E| ≤ 2` | `ℓ_t`, `scaleM = W²ℓ²η`, `tailT`, `ellStar` are not used by any target; the `Path/Scales` import cut needs only `etaT` (= merged `RBM.Gauss.etaT`, `GLoop.lean:75`, `etaT_eq_zt_im`); `scaleM` (which has `W²`) is not needed |
| 13 | other `d = 2` tokens of the portmap rows (`W^2:9`, `inv2:40`, `d=2:1`, `Z2/zdist2:55` in ConArgDet; `W^2:5`, `inv2:6`, `Z2:12` in WardResolvent) | — | `W²→W^d` (rows 3,5–7 and the `Checks` section), `W⁻²→W^{-d}` (rows 1,2,4,8), `Z2→Zd d`, `Fin W × Fin W → Fin (W^d)`; `d=2:1` is the module docstring | `zdist2` does not occur in the statements of the five key targets (no distance enters) |
| 14 | `sum_gloop_head`, `gloop_rotate` (used by the Ward proof): `Σ_b E_b = W^{-d}·1`, cyclic rotation of a loop by one pair | `W^{-d}` | pure algebra | exact |

All statements of rows 2–10 are for a fixed deterministic Hermitian `H`; no `≺`, no probability, no `N` (the scaling `N = (WL)^d` enters only through `Vtx` having `L^d W^d` sites).

### (ii) One concrete nondegenerate instance (`d = 3`, `L = 4`, `W = 2`)

Data: `N = (WL)^d = 512 = L^d W^d = 64·8` sites, `H` = a seeded random complex Hermitian `512×512` (`(A+Aᴴ)/√(4N)`, `H = Hᴴ` asserted), `E = 0.5`, `κ = 1` (`|E| = 0.5 ≤ 2−κ = 1`), `c = t₁ = 1/4`, `t₂ = 1/2` (`c ≤ t₁ ≤ t₂ ≤ 1`),
`z = z_{t₂} = E + (1−t₂)m^{(E)} = 0.375+0.484123i` (`Im z > 0`), `w = z̃ = √(t₂/t₁) z_{t₁} = 0.441942+1.02698i` (`Im w > 0`). `m = 1`, `p ∈ {1,2}` (so `1 ≤ m`, `1 ≤ p`), `k = 1`, `μ ∈ {[], [+], [−,+]}`, `a'` of the same length.
`loopMax` is exact over all `4^n·64^n` charges/labels for `n ∈ {1,2}` (block tensors, `loop`-vs-tensor sanity assert in the script).

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2063/inst.py` (numpy 2.0.2; Python only, no Lean). Verbatim output:

```
N=512 Wd=8 labels=64  z=(0.375+0.484123j)  w=ztTilde=(0.441942+1.02698j)
Ward div form: max|lhs-rhs| over 12 samples = 1.112e-16 ; largest sample (mu=[],a'=[],x=9): lhs=(0.20182705-0j) rhs=(0.20182705-0j)
  mu=[]: |lhs|=2.018e-01 rel.err=1.52e-16 ; with W^2 (d=2 factor) instead of W^d: rel.err=1.000
  mu=[True]: |lhs|=2.179e-04 rel.err=1.71e-16 ; with W^2 (d=2 factor) instead of W^d: rel.err=1.000
  mu=[False, True]: |lhs|=9.773e-07 rel.err=4.60e-16 ; with W^2 (d=2 factor) instead of W^d: rel.err=1.000
loopMax_z(1)=0.804630 loopMax_z(2)=0.082918 loopMax_w(1)=0.612283 loopMax_w(2)=0.047287
loopMax_two_mul_le_tilde m=1 p=1: LHS=0.082918 RHS=0.687480 slack=0.604562 holds=True
loopMax_two_mul_le_tilde m=1 p=2: LHS=0.082918 RHS=0.305149 slack=0.222231 holds=True
trace_gram_rpow_le k=1 p=1: max_b LHS/RHS = 0.981830 (<=1 required), sample RHS=4.769580
trace_gram_rpow_le k=1 p=2: max_b LHS/RHS = 0.979097 (<=1 required), sample RHS=1.693951
ztTilde_arith: C=693.000 eta_t1=0.726184 |z_t2-w|=0.546969 <=C(1-t1)=519.7500 ; |.|^2=0.299175<=C eta^2=365.4492 ; |.|^2/Im w=0.291315<=C eta=503.2458 ; eta=0.726184<=Im w=1.026980<=C eta=503.2458
1-t1 / eta_t1 vs 2/kappa: 1.0327955589886444 2.0  sqrt(t2/t1)= 1.4142135623730951 <=1/c= 4.0  (s-1)=0.4142 <= (t2-t1)/c=1.0000
```

Reading: both sides of `sum_gloop_ward_last_div` (`μ = []`, `x = 9`) are `0.20182705` (nonzero, equal to `1.5e-16` relative; the `μ = [+]`, `[−,+]` samples agree to `≤ 4.6e-16` relative, but those loop values are small, `2.2e-4`, `9.8e-7`); both sides of `loopMax_two_mul_le_tilde` are `0.082918 ≤ 0.687480` (`m = 1`, `p = 1`) and `0.082918 ≤ 0.305149` (`p = 2`). No hypothesis is external (no probabilistic or PT input), so no limit computation is needed.

### Verdicts

- `green_sub_green` (WardResolvent:25): PASS. Algebraic resolvent identity `G(z) − G(w) = (z−w)G(z)G(w)`, independent of `d`, `L`, `W`.
- `sum_gloop_ward_last_div` (WardResolvent:159): PASS with `W²` replaced by `W^d` in the denominator (rows 1–3; paper `WI_calL` has `W^d`). Special case `σ_1 = +`, `σ_n = −` of the paper's identity; the `(−, …, +)` case is not part of the target.
- `ztTilde_arith` (ConArgDet:537): PASS, `d`-free; the only scale fact it needs is `etaT` (row 12), already merged; no `d`-dimensional `Path/Scales` helper is required (`ellT`/`scaleM` unused by the targets).
- `trace_gram_rpow_le` (ConArgDet:834): PASS with `W²` → `W^d` (rows 5–7); `Fin W × Fin W → Fin (W^d)`.
- `loopMax_two_mul_le_tilde` (ConArgDet:1019): PASS, `d`-free statement; chain from rows 4, 7–9 closes with exact cancellation of `W^{±d}`.
- Overall verdict: PASS.

## (b) Script output — Sat Oct  3 19:44:08 UTC 2026

Branch `t/T2063`, files: `RBM3D/Induction/ConArgDet.lean` only (new, 1611 lines, imports `RBM3D.Induction.Split`, `RBM3D.Loop.GLoop`, `RBM3D.Green.EntryCore`, `Mathlib.Algebra.Order.Chebyshev`).
`RBM3D/Test/Axioms.lean` is unchanged: no registry line is needed (pre-check below).

```
$ cd RBM3D-wt/T2063 && git log --oneline -1 && git diff --stat main...t/T2063
e4d26e2 T2063: port WardResolvent and ConArgDet (S1-31) to d >= 3
RBM3D/Induction/ConArgDet.lean | 1611 ++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1611 insertions(+)
$ lake build RBM3D.Induction.ConArgDet      # run after the last edit of the file (tool log); idempotent re-run prints the second line only
✔ [3301/3301] Built RBM3D.Induction.ConArgDet (6.5s)
Build completed successfully (3301 jobs).
$ lake env lean RBM3D/Induction/ConArgDet.lean   # fresh compile of the committed file, no messages
lake env lean RBM3D/Induction/ConArgDet.lean  15.12s user 2.72s system 242% cpu 7.345 total
lake env lean exit=0
$ lake build        # whole library (root RBM3D.lean does not yet import the new module; the hub adds it at merge)
Build completed successfully (3784 jobs).
```

Registry pre-check (ST1-COMMON item 8): scratch `scratchpad/T2063/registry_precheck.lean` = `import RBM3D`, `import RBM3D.Induction.ConArgDet`, `#assert_rbm_axioms`; baseline = same without the second import.
```
$ lake env lean registry_precheck.lean ; echo exit=$?     (exit=0)   [new module]
axiom audit: 2216 theorems, 890 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 45 (borrowed 2, owed 31, structural 12).
$ lake env lean registry_base.lean ; echo exit=$?         (exit=0)   [baseline]
axiom audit: 2163 theorems, 884 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 45 (borrowed 2, owed 31, structural 12).
```
Difference: +53 theorems, +6 definitions (= the 59 public declarations); scan finds the same 45 premises (no new Prop-valued assumption; `IsGLoopProd` is concluded by `isGLoopProd_one`, `IsGLoopProd.mul`).

`#print axioms` of all 59 public declarations (`axcheck.lean`, `lake env lean`, exit 0): 59 of 59 lines read `depends on axioms: [propext, Classical.choice, Quot.sound]`. The five targets:
```
'RBM.green_sub_green' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.sum_gloop_ward_last_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.ztTilde_arith' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.trace_gram_rpow_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.loopMax_two_mul_le_tilde' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Target statements, extracted from the file by script (`extract.py`; `variable`s in force: `{n} [Fintype n] [DecidableEq n]` for `green_sub_green`; `(d L W : ℕ) [NeZero L]` explicit for `sum_gloop_ward_last_div`; `{c E t₁ t₂ : ℝ}` for `ztTilde_arith`; `{d L W} [NeZero L] [NeZero W] {H}` for the other two):
```
-- ConArgDet.lean:73
theorem green_sub_green {H : Matrix n n ℂ} {z w : ℂ}
    (hz : IsUnit (H - z • (1 : Matrix n n ℂ)))
    (hw : IsUnit (H - w • (1 : Matrix n n ℂ))) :
    green H z - green H w =
      (z - w) • (green H z * green H w) := by
-- ConArgDet.lean:312
theorem sum_gloop_ward_last_div [NeZero W]
    {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ}
    (hz : IsUnit (H - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)))
    (hz' : IsUnit (H - ((starRingEnd ℂ) z) •
      (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)))
    (hη : z.im ≠ 0)
    (μ : List Bool) (x : Zd d L) (a' : List (Zd d L))
    (hμ : μ.length = a'.length) :
    (∑ b : Zd d L,
      loopL d L W H z ⟨true :: μ ++ [false], x :: a' ++ [b]⟩) =
      (loopL d L W H z ⟨true :: μ, x :: a'⟩ -
        loopL d L W H z ⟨false :: μ, x :: a'⟩) /
        (2 * Complex.I * (W : ℂ) ^ d * (z.im : ℂ)) := by
-- ConArgDet.lean:850
theorem ztTilde_arith {κ : ℝ} (hc : 0 < c) (hκ : 0 < κ) :
    ∃ C > 0, ∀ E t₁ t₂ : ℝ, c ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ 1 → |E| ≤ 2 - κ →
      ‖zt E t₂ - ztTilde E t₁ t₂‖ ≤ C * (1 - t₁)
      ∧ ‖zt E t₂ - ztTilde E t₁ t₂‖ ^ 2 ≤ C * Gauss.etaT E t₁ ^ 2
      ∧ ‖zt E t₂ - ztTilde E t₁ t₂‖ ^ 2 / (ztTilde E t₁ t₂).im ≤ C * Gauss.etaT E t₁
      ∧ Gauss.etaT E t₁ ≤ (ztTilde E t₁ t₂).im
      ∧ (ztTilde E t₁ t₂).im ≤ C * Gauss.etaT E t₁ := by
-- ConArgDet.lean:1334
theorem loopMax_two_mul_le_tilde (hH : H.IsHermitian) {z w : ℂ} (hz : 0 < z.im)
    (hw : 0 < w.im) {m : ℕ} (hm : 1 ≤ m) {p : ℕ} (hp : 1 ≤ p) :
    loopMax d L W H z (2 * m)
      ≤ (m + 1 : ℝ) * (loopMax d L W H w (2 * m) + ‖z - w‖ ^ 2
        * ((z.im * w.im)⁻¹ * ∑ l ∈ Finset.range m, loopMax d L W H z (2 * l + 1)
          * loopMax d L W H w (p * (2 * (m - l) - 1)) ^ (1 / (p : ℝ)))) := by
-- ConArgDet.lean:1147
theorem trace_gram_rpow_le (hH : H.IsHermitian) {w : ℂ} (hw : 0 < w.im) {τ : List Bool}
    {c : List (Zd d L)} (h : τ.length = c.length + 1) (b : Zd d L) {p : ℕ} (hp : 1 ≤ p) :
    (trace (gram ℂ (blockCols (gchain d L W H w τ c) b) ^ p)).re ^ (1 / (p : ℝ))
      ≤ (W : ℝ) ^ d * (w.im)⁻¹ * loopMax d L W H w (p * (2 * τ.length - 1)) ^ (1 / (p : ℝ)) := by
```
RBM2D sources at `c9a24cf`: `Hierarchy/WardResolvent.lean:25` (`green_sub_green`), `:159` (`sum_gloop_ward_last_div`); `Induction/ConArgDet.lean:537` (`ztTilde_arith`), `:834` (`trace_gram_rpow_le`), `:1019` (`loopMax_two_mul_le_tilde`).

Statement diff against RBM2D (`stmtdiff.py`: statements of all public declarations of both RBM2D files, text up to the top-level `:=`, rename map applied to the RBM2D text, whitespace-insensitive; rename map: `BlockIndex L W → Vtx d L W`, `Z2 L → Zd d L`, `gloop L W → loopL d L W`, `gloopProd/gchain/Eblk/loopMax/IsGLoopProd/gchainMixed L W → … d L W`, `LoopIdx → Loop.LoopIdx`, `(W:ℂ)⁻¹^2 → ((W:ℂ)^d)⁻¹`, `(W:ℝ)⁻¹^2 → ((W:ℝ)^d)⁻¹`, `(W:ℝ)^2 → (W:ℝ)^d`, `Fin W × Fin W → Fin (W^d)`, `Gauss.spectralZ/spectralM → zt/mE`, `Path.etaT → Gauss.etaT`, `Gsig → Gres`, `Gsig_eq_green_zSig/Gsig_eq_add_smul_mul/Gsig_mul_conjTranspose → Gres_…`):
```
RBM2D public declarations (statement up to :=): 59
identical after renaming: 59
missing in 3D: []
differ: 0
public in 3D file only: []
(the same script with the rename map switched off: identical 16, differ 43)
```
Residual differences: none in the 59 statements. Binders differ only by `variable`: `d` is added to `L W` (explicit in `section TwoLoop`, as RBM2D's `(L W)`; implicit elsewhere).

`d = 2` tokens (`tokens.out`, own regexes; the portmap's counts use its own rules): 
```
RBM2D WardResolvent (c9a24cf, all text): {'W2': 5, 'inv2': 6, 'd=2': 0, 'Z2/zdist2': 12, 'Fin W x Fin W': 0, 'BlockIndex': 18, 'Path.etaT': 0, 'scaleM/ellT/tailT/ellStar/Meta/ellz': 0}
RBM2D ConArgDet (c9a24cf, all text): {'W2': 9, 'inv2': 34, 'd=2': 1, 'Z2/zdist2': 55, 'Fin W x Fin W': 21, 'BlockIndex': 148, 'Path.etaT': 24, 'scaleM/ellT/tailT/ellStar/Meta/ellz': 0}
RBM3D ConArgDet (code, comments stripped): {'W2': 0, 'inv2': 0, 'd=2': 0, 'Z2/zdist2': 0, 'Fin W x Fin W': 0, 'BlockIndex': 0, 'Path.etaT': 0, 'scaleM/ellT/tailT/ellStar/Meta/ellz': 0}
```
Exponent changes (statements containing `^ d`, by script): `sum_gloop_two_ward`, `sum_gloop_ward_last` (`W⁻² → W^{-d}`), `sum_gloop_ward_last_div` (denominator `2i W² Im z → 2i W^d Im z`), `trace_Eblk_mul_mul_conjTranspose`, `ward_chain_row`, `ward_chain_row'`, `sum_norm_gchain_row_sq_le`, `sum_bw_mul` (row average `W^{-d} ∑_{α ∈ Fin (W^d)}`), `blockCols`, `blockSel` (fibre `Fin (W^d)`), `blockSel_mul_transpose` (`W^d • E_b`), `trace_gram_blockCols_pow` (`(W^d)^{p+1}`), `trace_gram_rpow_le` (`W^d (Im w)⁻¹`). Dimension-free as ported: `green_sub_green`, `ztTilde_arith`, `loopMax_two_mul_le_tilde`, `wmass_gchain_mul_gchain_le` (`W^{-d} W^d` cancel).

Compiled nonempty instances of the five targets (`Checks` section; `d = 3`, `L = 3`, `W = 2`: `Vtx 3 3 2 = Zd 3 3 × Fin 8`, 216 sites, 27 labels; `cad_Hd = diag(x.2)` Hermitian, not scalar; `E = 0`, `z = zt 0 (1/2)` with `Im z = 1/2` (`cad_im_z`), `w = ztTilde 0 (1/4) (1/2)` with `Im w = 3√2/4` (`cad_im_w'`); every hypothesis is discharged, none remains):
```
-- ConArgDet.lean:1403
example :
    green cad_Hd (zt 0 (1 / 2)) - green cad_Hd (ztTilde 0 (1 / 4) (1 / 2))
      = (zt 0 (1 / 2) - ztTilde 0 (1 / 4) (1 / 2)) •
          (green cad_Hd (zt 0 (1 / 2)) * green cad_Hd (ztTilde 0 (1 / 4) (1 / 2))) :=
  green_sub_green (isUnit_sub_smul_one_of_im_ne_zero cad_Hd_herm cad_z_pos.ne')
    (isUnit_sub_smul_one_of_im_ne_zero cad_Hd_herm cad_im_w.ne')
-- ConArgDet.lean:1413
example :
    (∑ b : Zd 3 3, loopL 3 3 2 cad_Hd (zt 0 (1 / 2))
        ⟨true :: [false, true] ++ [false], (0 : Zd 3 3) :: [0, 1] ++ [b]⟩)
      = (loopL 3 3 2 cad_Hd (zt 0 (1 / 2)) ⟨true :: [false, true], (0 : Zd 3 3) :: [0, 1]⟩
          - loopL 3 3 2 cad_Hd (zt 0 (1 / 2)) ⟨false :: [false, true], (0 : Zd 3 3) :: [0, 1]⟩)
        / (2 * Complex.I * (2 : ℂ) ^ 3 * ((zt 0 (1 / 2)).im : ℂ)) :=
  sum_gloop_ward_last_div 3 3 2
    (isUnit_sub_smul_one_of_im_ne_zero cad_Hd_herm cad_z_pos.ne')
    (isUnit_sub_smul_one_of_im_ne_zero cad_Hd_herm (cad_conj_im_ne cad_z_pos)) cad_z_pos.ne'
    [false, true] 0 [0, 1] rfl
-- ConArgDet.lean:1451
example :
    ∃ C > 0, ‖zt (1 / 2) (1 / 2) - ztTilde (1 / 2) (1 / 4) (1 / 2)‖ ≤ C * (1 - 1 / 4)
      ∧ ‖zt (1 / 2) (1 / 2) - ztTilde (1 / 2) (1 / 4) (1 / 2)‖ ^ 2
          ≤ C * Gauss.etaT (1 / 2) (1 / 4) ^ 2
      ∧ ‖zt (1 / 2) (1 / 2) - ztTilde (1 / 2) (1 / 4) (1 / 2)‖ ^ 2
          / (ztTilde (1 / 2) (1 / 4) (1 / 2)).im ≤ C * Gauss.etaT (1 / 2) (1 / 4)
      ∧ Gauss.etaT (1 / 2) (1 / 4) ≤ (ztTilde (1 / 2) (1 / 4) (1 / 2)).im
      ∧ (ztTilde (1 / 2) (1 / 4) (1 / 2)).im ≤ C * Gauss.etaT (1 / 2) (1 / 4) := by
  obtain ⟨C, hC, h⟩ := ztTilde_arith (c := 1 / 4) (κ := 1) (by norm_num) (by norm_num)
  exact ⟨C, hC, h (1 / 2) (1 / 4) (1 / 2) le_rfl (by norm_num) (by norm_num)
    (by rw [abs_of_pos (by norm_num)]; norm_num)⟩
-- ConArgDet.lean:1465
example :
    loopMax 3 3 2 cad_Hd (zt 0 (1 / 2)) (2 * 1)
      ≤ ((1 : ℕ) + 1 : ℝ) * (loopMax 3 3 2 cad_Hd (ztTilde 0 (1 / 4) (1 / 2)) (2 * 1)
        + ‖zt 0 (1 / 2) - ztTilde 0 (1 / 4) (1 / 2)‖ ^ 2
          * (((zt 0 (1 / 2)).im * (ztTilde 0 (1 / 4) (1 / 2)).im)⁻¹
            * ∑ l ∈ Finset.range 1, loopMax 3 3 2 cad_Hd (zt 0 (1 / 2)) (2 * l + 1)
              * loopMax 3 3 2 cad_Hd (ztTilde 0 (1 / 4) (1 / 2)) (1 * (2 * (1 - l) - 1))
                ^ (1 / ((1 : ℕ) : ℝ)))) :=
  loopMax_two_mul_le_tilde cad_Hd_herm cad_z_pos cad_im_w le_rfl le_rfl
-- ConArgDet.lean:1488
example :
    (trace (gram ℂ (blockCols (gchain 3 3 2 cad_Hd (ztTilde 0 (1 / 4) (1 / 2)) [true] [])
        (0 : Zd 3 3)) ^ 1)).re ^ (1 / ((1 : ℕ) : ℝ))
      ≤ (2 : ℝ) ^ 3 * ((ztTilde 0 (1 / 4) (1 / 2)).im)⁻¹
        * loopMax 3 3 2 cad_Hd (ztTilde 0 (1 / 4) (1 / 2)) (1 * (2 * [true].length - 1))
          ^ (1 / ((1 : ℕ) : ℝ)) :=
  trace_gram_rpow_le cad_Hd_herm cad_im_w rfl 0 le_rfl
```
Further examples in the same section (same data, not shown): `sum_gloop_ward_last`, `sum_gloop_two_ward`, `loopMax_two_mul_le_tilde` at `m = p = 2`, `trace_gram_rpow_le` at `τ = (+,−)`, `p = 2`, `wmass_gchain_mul_gchain_le`, `ward_chain_row`. Value checks at `H = 0`, `z = i` (both proved, `W^d = 8`):
```
-- ConArgDet.lean:1571
private theorem cad_ward_div_value (x : Zd 3 3) :
    (∑ b : Zd 3 3, loopL 3 3 2 (0 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) Complex.I
        ⟨true :: ([] : List Bool) ++ [false], x :: ([] : List (Zd 3 3)) ++ [b]⟩) = 1 / 8 := by
-- ConArgDet.lean:1592
private theorem cad_check_ward_row (a0 : Zd 3 3) :
    ∑ α : Fin (2 ^ 3), ∑ k : Vtx 3 3 2,
        (Complex.normSq (gchain 3 3 2 (0 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) Complex.I
          ([] ++ [true]) [] (a0, α) k) : ℂ) = 8 := by
```
(`cad_ward_div_value`: the sum over the 27 labels is `1/8`, the `d = 3` value `(i−(−i))/(2i·8·1)`; the `d = 2` factor `W² = 4` would give `1/4`.)

Name-clash grep (all of `RBM3D/` in the main worktree and in the T2063 worktree, any namespace, every one of the 59 new public short names, python scan; plus `grep -rnE` for the five targets, both with `ConArgDet.lean` excluded):
```
new public names: 59
clashes by short name (any namespace, all of RBM3D/ in main and worktree): 0
$ grep -rnE "(theorem|def|lemma) (green_sub_green|sum_gloop_ward_last_div|ztTilde_arith|loopMax_two_mul_le_tilde|trace_gram_rpow_le)\b" RBM3D --include='*.lean' | grep -v Induction/ConArgDet.lean
(no output)
```
Imports (transitive closure of `RBM3D.Induction.ConArgDet`: itself and these 20 modules, python scan of the `import` lines): `Induction.Split Loop.GLoop Green.EntryCore Loop.GLoopFlow Gauss.FlowCalculus Gauss.Model Defs.Semicircle Analysis.Resolvent Defs.Lattice Loop.TreeRep Gauss.FineModel Propagator.Props4 Gauss.SteinMatrix Loop.Partition Defs.Sizes Propagator.Basic Gauss.Stein Defs.Params Defs.Block Defs.Neighbours`: no ST-2…ST-6 file.

Port source (rule 5.2): RBM2D `c9a24cf` (`git -C ../RBM2D --no-optional-locks log -1 --format=%h` = `9e0f275` is RBM2D's HEAD; the port is from `c9a24cf` as the ticket pins it).
```
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Hierarchy/WardResolvent.lean RBM2D/Induction/ConArgDet.lean
 RBM2D/Hierarchy/WardResolvent.lean |  31 ---
 RBM2D/Induction/ConArgDet.lean     | 409 ++-----------------------------------
 2 files changed, 13 insertions(+), 427 deletions(-)
```

### Narrative
1. `ConArgDet.lean` = Part 1 (`namespace RBM`: the 6 public declarations of RBM2D `Hierarchy/WardResolvent`) + Part 2 (`namespace RBM.Ind`: the 53 of RBM2D `Induction/ConArgDet`) + `Checks`. All 59 public declarations are ported under RBM2D's names; none is dropped (`grep -n unused docs/reports/T2015-portmap.md` finds no entry for these two files). No hypothesis added, no statement weakened, no pinned or frozen signature touched; no `sorry`, `admit`, `axiom`, `native_decide`.
2. Vocabulary (merged): `Gsig H z s → Gres H z s`, `gloop L W H z I → loopL d L W H z I` (`RBM3D/Loop/GLoopFlow.lean`), `gchain`, `loopMax`, `symIdx`, `wmass`, `bw`, `sum_bw`, `gchain_conjTranspose`, `gchain_mul_Eblk`, `sum_norm_inner_sq_le_trace_pow`, `norm_gloop_le_of_symIdx_le` from `Induction/Split.lean` (T2033), `green` from `Green/EntryCore.lean` (T2029, imported, not copied), `Gauss.spectralZ_im`, `spectralM_im`, `norm_spectralM` from `Gauss/FlowCalculus.lean` (T2030).
3. Private copies (`cad_` prefix, rule 3(E)): `cad_gloopProd_nil/cons/append` (private in `GLoopFlow.lean:391-401` and in `Split.lean`), `cad_Gres_conjTranspose` (private in `Split.lean`), `cad_Gres_true/false`, `cad_loopL_eq`, `cad_gloop_rotate`, `cad_sum_gloop_head`, `cad_sum_Eblk` (RBM2D `Hierarchy/Loops.lean:51,54,68,99-147`, `Defs/Model.lean:83`), and RBM2D's own private `green_sub_green_conj`.
4. `Path/Scales` cut: the only name RBM2D `ConArgDet` takes from it is `Path.etaT` (24 occurrences; the scales `scaleM/ellT/tailT/ellStar/Meta/ellz` occur 0 times, `tokens.out`). It is the merged `RBM.Gauss.etaT` (`RBM3D/Loop/GLoop.lean:75`, `η_t = (1−t) Im m^{(E)}`), so no private copy of an ST-2 helper is needed; no `d`-dimensional scale enters any statement.
5. Reuse list of the ticket: `loopMax_odd_sq_le`, `norm_gloop_le_of_le_abs_im` are not used by `ConArgDet` (not copied). RBM2D's `gloop`, `Gsig` take an arbitrary matrix `H` and an arbitrary parameter `z`, and the targets need two parameters `z`, `w = z̃_{t₁}` at one `H` (`loopMax_two_mul_le_tilde`), so the ported statements use the merged general forms `loopL`, `Gres` (same choice as T2033); `Gauss.gloop`, `Gauss.Gsig` of `GLoop.lean` are their `(ω,E,t)` cases (`gloop_eq_loopM`, `Gsig_eq_Gres`, `GLoopFlow.lean`).
6. Ward at `d ≥ 3`: `E_a = (W^d)⁻¹ 1_{[a]}` gives `∑_b E_b = (W^d)⁻¹ 1` (`cad_sum_Eblk`), hence `W^{-d}` in `sum_gloop_two_ward`, `sum_gloop_ward_last`, and `W^d` in the divided form: the case `σ₁ = +`, `σ_n = −` of the paper's `WI_calL` (`1_2:1036-1042`). The value check `cad_ward_div_value` confirms the factor numerically at `W^d = 8`.
7. `ztTilde_arith` keeps RBM2D's `∃ C > 0` form (the ticket pins the statement); the constants of its proof are `K = (3/c+1)(2/κ)`, `C = (3/c+1)+K²+c⁻¹` (section (a) row 11).
8. Registry: no new `Prop`-valued assumption; `Test/Axioms.lean` untouched.


## (c) Verified Mathlib and merged names (`#check` in `scratchpad/T2063/checknames.lean`, output read; names new relative to the RBM2D text; all other names are those of the RBM2D text and compile)

- `Bool.false_eq_true`, `Bool.not_false`, `Bool.not_true`, `List.nil_append`, `Complex.I_im`, `Complex.conj_conj`, `Complex.ofReal_one`, `pow_ne_zero`: exist.
- `Finset.sum_ite_eq`: exists, `(∑ x ∈ s, if a = x then b x else 0) = if a ∈ s then b a else 0`.
- `Matrix.conjTranspose_nonsing_inv`, `Matrix.conjTranspose_one`, `Matrix.conjTranspose_smul`, `Matrix.conjTranspose_sub`: exist.
- `Matrix.nonsing_inv_eq_ringInverse : A⁻¹ = Ring.inverse A`, `Matrix.trace_sum`, `Matrix.isHermitian_zero`: exist.
- `Matrix.isHermitian_diagonal_iff : (diagonal d).IsHermitian ↔ ∀ i, IsSelfAdjoint (d i)`; `IsSelfAdjoint`: exist.
- Merged: `RBM.Gauss.trace_Eblk (d L W) (a) : (Eblk d L W a).trace = 1`, `RBM.Gauss.spectralZ_im`, `RBM.Gauss.spectralM_im`, `RBM.Gauss.norm_spectralM`, `RBM.mE_im`, `RBM.zt_im`: exist.
- Verified absent in RBM3D (clash scan above): none of the 59 new public names exists elsewhere.

## (d) Open issues and paper-delta candidates

- `T2063a`: `sum_gloop_ward_last_div` and `sum_gloop_ward_last` are the case `σ₁ = +`, `σ_n = −` of `WI_calL` (`1_2:1036-1042`, stated for `σ₁ = −σ_n`, both orders; right side `(2i W^d η_t)⁻¹(𝓛^{(n-1),+} − 𝓛^{(n-1),−})`, here with `Im z` for `η_t`, `z = z_t`: `etaT_eq_zt_im`); the `σ₁ = −`, `σ_n = +` case is not ported (as in RBM2D). A special case, not the general statement.
- `T2063b`: this file is the deterministic part of `lem_ConArg` (`3_5:42-57`; the paper's proof at `3_5:60` is "exactly the same as … Lemma 5.1 in [YY_25]"): (6.3)–(6.12) for a fixed Hermitian `H`, constant `C_m = m+1`; the probabilistic lemma is S1-32 (`STConArg`), not here.
- `T2063c`: namespaces: the 6 WardResolvent declarations are in `RBM` (`RBM.green_sub_green`, `RBM.sum_gloop_ward_last_div`, …), as RBM2D; the 53 others in `RBM.Ind`. Names `trace_Eblk_gloopProd_Gsig_conjTranspose`, `gloopProd_Gsig_conjTranspose_Eblk` keep RBM2D's `Gsig` in the name (they mention `Gres` in the statement).
- Observation for the dispatcher (rule 3(E)): a token scan of RBM2D at `c9a24cf` finds only 7 of the 59 names used outside the two files (`green_sub_green`, `green_sub_green_conj'`, `sum_gloop_ward_last_div`, `isUnit_sub_smul_one_of_im_ne_zero`, `ztTilde`, `ztTilde_arith`, `loopMax_two_mul_le_tilde`); the other 52 stay public here because the ticket says "every other public declaration is ported". Privatizing or prefixing them is a dispatcher decision.
- Observation: RBM2D HEAD `9e0f275` has moved since `c9a24cf` (diff-stat above); this port follows `c9a24cf`.
- No obstruction; no (a′) correction: the section (a) exponent table and instance agree with the compiled statements (the preflight numeric instance is `L = 4`, the Lean instances `L = 3`).
