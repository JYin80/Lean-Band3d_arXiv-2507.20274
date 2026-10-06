Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 13:58:33 UTC 2026

Notation: `κ₁ := πκ`; `c := κ₁⁵/2048`; "solution at z" = `BASelf d L g z m`. All merged inputs read from the files: `BASelf_sub_le` (ImmLower.lean:252: `(Im m² + Im m'²)‖m − m'‖ ≤ 2‖z − z'‖` for solutions at `Im z, Im z' ≥ 0`, no condition on `d, L, g`), `BAm_norm_le_one` (Ward.lean:136: `‖m‖ ≤ 1` for solutions at `Im z ≥ 0`), `BAbulk_iff_exists` (MFixedPoint.lean:830: for `κ > 0`, `BAbulk κ E ↔ ∃ m, BASelf (E:ℂ) m ∧ πκ ≤ Im m`), `BAm_real_eq_of_self` (:824), `BASelf_of_tendsto` (Boundary.lean:164: closedness of `(self_m)`, `Im m > 0`, `Im zs k ≥ 0`), `BAm_im_lower_of_bulk` (ImmLower.lean:424: `(πκ)⁵/64 ≤ Im m(E+iη)`, `0 < η ≤ 1`), `BAm_im_ge_mul` (:327: `η κ'²/(η+3)² ≤ Im m(E+iη)` from `BAReal κ' E m`).

### (i) Exponent table

| # | quantity | value | constraint to satisfy | slack |
|---|---|---|---|---|
| 1 | `κ₁ ≤ 1` (from `BAbulk κ E`, `κ>0`) | `κ₁ ≤ Im m_E ≤ ‖m_E‖ ≤ 1` (`BAm_norm_le_one`, `Complex.im_le_norm`) | used in row 8 (and row 9: `c ≤ 1 = C`) | `κ₁ = 0.828160` at the instance |
| 2 | target 1 modulus: `‖m−m'‖ ≤ ‖z−z'‖/c²` | factor `1/c²` | `2c² ≤ Im m² + Im m'²` when `c ≤ Im m, Im m'`; then divide `(·)‖Δm‖ ≤ 2‖Δz‖` by `2c²` | none needed (exact), `c > 0` only |
| 3 | window radius `δ₀ = κ₁³/8` (target 2, 7) and `η_k ≤ κ₁³/8` | `κ₁³/8` | `‖E−(x+iη)‖ ≤ |x−E|+η ≤ κ₁³/4`; `κ₁²‖m_E−m_η‖ ≤ 2‖Δz‖ ≤ κ₁³/2`, so `‖m_E−m_η‖ ≤ κ₁/2`, `Im m_η ≥ κ₁/2` | closes with equality (`κ₁³/2 = κ₁²·κ₁/2`), no slack; any radius `≤ κ₁³/8` also works |
| 4 | bulk constant on the window `κ/2` | `π(κ/2) = κ₁/2` | `κ₁/2 ≤ Im m_x`, `m_x` the subsequential limit (`Im m_x ≥ κ₁/2 > 0` by `ge_of_tendsto` through `Complex.continuous_im`) | equality, `κ₁/2 > 0` |
| 5 | Lipschitz constant of `ρ` (target 3) | `1/(π³κ²) = 1/(πκ₁²)` | `2κ₁²‖m_x−m_y‖ ≤ 2|x−y|` (both `Im ≥ κ₁`), `|Δ Im| ≤ ‖Δm‖`, divide by `π` | exact |
| 6 | rate (target 4) | `2η/(π³κ²) = 2η/(πκ₁²)` | `κ₁²‖m_E−m'‖ ≤ 2η` at `z−z' = −iη`, `‖·‖=η`, divide by `π` | exact; `→ 0` as `η ↓ 0` (squeeze for the `𝓝[>] 0` limit of `UNDens`) |
| 7 | target 5, branch `0<η≤1` | `(π·κ/2)⁵/64 = κ₁⁵/2048` | `BAm_im_lower_of_bulk` at `κ/2` (needs `BAbulk (κ/2) x` = target 2, `κ/2 > 0`) | exact |
| 8 | target 5, branch `1<η≤10` | `(κ₁/2)²·η/(η+3)² ≥ (κ₁/2)²/169 = κ₁²/676` | `η ≥ 1`, `(η+3)² ≤ 169`; need `κ₁²/676 ≥ κ₁⁵/2048`, i.e. `κ₁³ ≤ 2048/676 = 3.0296`; row 1 gives `κ₁³ ≤ 1` | factor `3.03` |
| 9 | `UNDens'` constants (target 6) | `c = κ₁⁵/2048`, `C = K = 1`, `Lp = 1/c² = 2048²/κ₁¹⁰`, all fixed before `∀ᶠ n`, depend on `κ` only | `c ≤ Im m ≤ ‖m‖ ≤ 1` (rows 7, 8, `Complex.im_le_norm`, `BAm_norm_le_one`); `Lp`: row 2 at both points (`|Im Δ| ≤ ‖Δm‖`, `‖⟨x,η⟩−⟨y,η⟩‖ = |x−y|`); box: `Im z ≤ 1 ≤ 10` so row 7/8 apply at `x = z.re`, `η = z.im` | `c ≤ 1 = C` since `κ₁ ≤ 1`; `δ ≤ δ₀` for `UNDens` and the box clause |
| 10 | pin `δ₀` (target 7) | `κ₁³/8 = (πκ)³/8` | `0 < δ₀`; first conjunct = target 6; second = `hb.mono` with target 2 at `|x−E| ≤ δ ≤ δ₀` | positive for `κ > 0` |
| 11 | compactness (target 2) | `η_k = κ₁³/(8(k+1)) → 0`, `m_{η_k} ∈ closedBall 0 1` | `tendsto_subseq_of_bounded` (Bolzano–Weierstrass) gives `φ, m_x`; `x+iη_{φ k} → x`, `Im ≥ 0` for `BASelf_of_tendsto` | no extra hypothesis (`3 ≤ L`, `0 < g` not needed) |
| 12 | unused premises of the pin | `3 ≤ d`, `Admissible 𝔠 𝔡` | none of the targets 1–7 uses them (`3 ≤ L` only as `NeZero (sz.L n)` from `Sizes.three_le_L`); `g = sz.lam n` has no sign condition | irrelevant to the closing of any row |

No exponent of the paper (`W`, `N`, `ℓ`) enters; the constants are lossy and only existence uniform in `n, L, g, d` is needed. Every row closes.

### (ii) One concrete nondegenerate instance

`d = 3`, `L = 4` (`N_blocks = L^d = 64`), `g = 3/10`, spectrum `g·2Σ_j cos(2πk_j/4)` (block adjacency eigenvalues, `L ≥ 3`), `E = 0`; sequence `L_n ≡ 4`, `lam_n ≡ 3/10`, `W_n = (2(n+1))⁵` (the shape of `clsSz`, UNPins.lean:776-781), `(𝔠, 𝔡) = (1/6, 1/10)`. Hypotheses of target 7: `3 ≤ d` (d = 3), `Admissible` (rows printed for `n = 0,1,5,100`; `W_n → ∞` so `SizeTendsto` holds), `κ > 0` and `BAbulk` at every `n` (constant sequence, `ρ(E) = κ`). `m` is computed by Newton on `m = N⁻¹ Σ (v_i − z − m)⁻¹` along a geometric `η`-path from 2 down to the target `η` (real axis: `η = 10⁻¹³`, then Newton at `Im z = 0`). Every printed ratio is the quantity of the target divided by its Lean-side bound, with `κ` the actual `ρ(E)`; the window has 9 points of `[E−δ₀, E+δ₀]`, `η` 12 log points of `[10⁻⁶, 10]`.

Command (scratch Python, not Lean):
`python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2300/inst.py`

Output (verbatim):
```
N= 64 E= 0.0 residual(self_m at E)=8.37e-18 Im m_E=0.828160 kappa=rho(E)=0.263612
pi*kappa=0.828160 <=1: True ; delta0=(pi k)^3/8=7.100e-02 ; c=(pi k)^5/2048=1.902e-04 ; Lp=1/c^2=2.764e+07 ; C=K=1
T2 min rho(x)/(kappa/2)=1.9989 (>=1)
T5 min Im m(x+i eta)/c=517.8537 (>=1)  ; max |m|=0.8282 (<=1=K)
T1 max ||Dm||/(||Dz||/c^2)=1.297e-08 (<=1)
T3 max |Drho|/(|Dx|/(pi^3 k^2))=0.0079 (<=1)
T4 max |Im m(E+i eta)/pi - rho|/(2 eta/(pi^3 k^2))=0.1229 (<=1)
T5 (1<eta<=10) min Im m/((k1/2)^2/169)=97.09 (>=1); (k1/2)^2/169=1.015e-03 >= c=1.902e-04: True
n=0 W=32 N=2097152: W>=N^(1/6): True ; W^(-3/2+1/10)=7.813e-03<=lam=0.30<=10: True
n=1 W=1024 N=68719476736: W>=N^(1/6): True ; W^(-3/2+1/10)=6.104e-05<=lam=0.30<=10: True
n=5 W=248832 N=986049380773527552: W>=N^(1/6): True ; W^(-3/2+1/10)=2.791e-08<=lam=0.30<=10: True
n=100 W=336323216032 N=2434728366692103168022452217317425152: W>=N^(1/6): True ; W^(-3/2+1/10)=7.287e-17<=lam=0.30<=10: True
```

Reading: `κ = ρ(E) = 0.263612 > 0`, `κ₁ = 0.828160 ≤ 1` (row 1), `δ₀ = 7.100·10⁻²`, `c = 1.902·10⁻⁴`: target 2 min ratio 1.9989 ≥ 1 (the window stays in the `κ/2`-bulk, not collapsed: `δ₀ > 0`, 9 window points); target 5 min ratio 517.85 ≥ 1 for `η ∈ [10⁻⁶,10]`, and on `η ∈ {1.5,3,6,10}` the row 8 form holds with ratio 97.09 and `(κ₁/2)²/169 = 1.015·10⁻³ ≥ c`; `‖m‖ ≤ 0.8282 ≤ K = 1`; target 1 max ratio `1.3·10⁻⁸ ≤ 1`; target 3 max 0.0079 ≤ 1; target 4 max 0.1229 ≤ 1 (the `ρ`-limit clause of `UNDens` with rate). No hypothesis of any target is vacuous: `N ≠ 0`, nonempty window, `κ > 0`, no sign condition on `g` needed.

External hypothesis: none. The proof is unconditional (D6 closedness, D7 two-point estimate, Ward bound are merged theorems with all premises discharged above: `0 ≤ Im z`, `Im m > 0`, `NeZero L`). Limit computation for the one limit the targets contain: `|π⁻¹ Im m(E+iη) − ρ(E)| ≤ 2η/(π³κ²)` and `2η/(π³κ²) → 0` as `η ↓ 0` at `κ = 0.263612`; numerically the ratio is ≤ 0.1229 for `η ∈ [10⁻⁸, 1]` (target 4 row above).

### Verdicts

- Target 1 `BAm_sub_le_of_im` (R1): PASS (row 2).
- Target 2 `BAbulk_window` (R2): PASS (rows 3, 4, 11; closes with equality, no loss of constants).
- Target 3 `BArho_lip_of_bulk` (R3): PASS (row 5).
- Target 4 `BArho_rate_of_bulk` (R4): PASS (row 6).
- Target 5 `BAm_im_lower_window` (R5): PASS (rows 7, 8; needs `κ₁ ≤ 1`, row 1).
- Target 6 `unDens'_ba` (R6): PASS (row 9; `UNDens'` clauses (a), (b), (c) and box verified above; constants before `∀ᶠ n`).
- Target 7 `unDensBARow'_holds` (R7): PASS (row 10; premises `3 ≤ d`, `Admissible` unused).
- Instances (I1)–(I5): hypotheses discharged by the same data; (I2)–(I4) need only `0 < κ` and `BAbulk` of the merged flow point (ImmLower.lean:456-468 recipe) and the merged `S0_bulk`, `clsκ_pos`.

Overall: PASS.

### (a′) Preflight corrections

None. Every row of (a) agrees with the proved statements (constants `δ₀ = (πκ)³/8`, `c = (πκ)⁵/2048`, `C = K = 1`, `Lp = 1/c²`); no verdict changes.

## (b) Script output — Tue Oct  6 14:10:18 UTC 2026

### Build, commit, scope
```
$ lake build RBM3D.BA.MReg 2>&1 | tail -1
Build completed successfully (3754 jobs).
$ wc -l RBM3D/BA/MReg.lean
     384 RBM3D/BA/MReg.lean
$ git log --oneline -1
a4d82d3 T2300: BA-C2 BA/MReg regularity of m(., lambda) on the bulk window, UNDensBARow' proved
$ git diff --stat main...t/T2300
 RBM3D/BA/MReg.lean     | 384 +++++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean |   1 -
 2 files changed, 384 insertions(+), 1 deletion(-)
$ grep -cE "sorry|admit|native_decide|^axiom| axiom " RBM3D/BA/MReg.lean
0
```
Registry diff (`git diff main...t/T2300 -- RBM3D/Test/Axioms.lean`, tail):
```
+++ b/RBM3D/Test/Axioms.lean
@@ -231,7 +231,6 @@ def owedProps : List Name :=
    `RBM.Univ.UNEMCTE2RowBA, -- bulk universality, block Anderson (T2241, BA-C1b: owed; owner the model-generic UN rows at `UNKind.ba`)
    `RBM.Univ.UNJakUywRowBA, -- bulk universality, block Anderson (T2241, BA-C1b: owed; owner the model-generic UN rows at `UNKind.ba`)
    `RBM.Univ.UNClaimRowBA, -- bulk universality, block Anderson (T2241, BA-C1b: owed; owner the model-generic UN rows at `UNKind.ba`)
-   `RBM.Univ.UNDensBARow', -- bulk universality, block Anderson (T2241, BA-C1b: owed; owner BA-C2, `unDens'_freeConvST`)
    `RBM.Univ.UNTrLocalBARow, -- bulk universality, block Anderson (T2241, BA-C1b: owed; owner BA-N1)
    `RBM.Univ.UNTrLocalInitBARow', -- bulk universality, block Anderson (T2241, BA-C1b: owed; owner BA-N1, BA model at coupling `λ e^{t*/2}`, BA-D8)
    `RBM.Univ.UNNormBARow, -- bulk universality, block Anderson (T2241, BA-C1b: owed; owner BA-N1, `‖V‖ + λ‖Ψ‖`)
```

### `#print axioms` of the 7 public theorems (`lake env lean`, exit 0)
```
'RBM.BA.BAm_sub_le_of_im' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAbulk_window' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BArho_lip_of_bulk' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BArho_rate_of_bulk' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAm_im_lower_window' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unDens'_ba' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unDensBARow'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Target statements (extracted from `RBM3D/BA/MReg.lean` by script)
```lean
theorem BAm_sub_le_of_im (d L : ℕ) [NeZero L] (g c : ℝ) (z z' : ℂ) (hc : 0 < c) (hz : 0 < z.im) (hz' : 0 < z'.im)
    (h1 : c ≤ (BAm d L g z).im) (h2 : c ≤ (BAm d L g z').im) :
    ‖BAm d L g z - BAm d L g z'‖ ≤ ‖z - z'‖ / c ^ 2

theorem BAbulk_window (d L : ℕ) [NeZero L] (g κ E x : ℝ) (hκ : 0 < κ) (hb : BAbulk d L g κ E)
    (hx : |x - E| ≤ (Real.pi * κ) ^ 3 / 8) : BAbulk d L g (κ / 2) x

theorem BArho_lip_of_bulk (d L : ℕ) [NeZero L] (g κ x y : ℝ) (hκ : 0 < κ) (hx : BAbulk d L g κ x)
    (hy : BAbulk d L g κ y) :
    |BArho d L g x - BArho d L g y| ≤ |x - y| / (Real.pi ^ 3 * κ ^ 2)

theorem BArho_rate_of_bulk (d L : ℕ) [NeZero L] (g κ E : ℝ) (hκ : 0 < κ) (hb : BAbulk d L g κ E)
    (η : ℝ) (hη : 0 < η) :
    |(BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)).im / Real.pi - BArho d L g E| ≤
      2 * η / (Real.pi ^ 3 * κ ^ 2)

theorem BAm_im_lower_window (d L : ℕ) [NeZero L] (g κ E x η : ℝ) (hκ : 0 < κ) (hb : BAbulk d L g κ E)
    (hx : |x - E| ≤ (Real.pi * κ) ^ 3 / 8) (hη : 0 < η) (hη10 : η ≤ 10) :
    (Real.pi * κ) ^ 5 / 2048 ≤ (BAm d L g ((x : ℂ) + (η : ℂ) * Complex.I)).im

theorem unDens'_ba (d : ℕ) (sz : Sizes d) (κ E : ℝ) (hκ : 0 < κ)
    (hb : ∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) κ E) (δ : ℝ) (hδ : 0 < δ)
    (hδ' : δ ≤ (Real.pi * κ) ^ 3 / 8) :
    UNDens' (fun n => BAm d (sz.L n) (sz.lam n)) E (fun n => BArho d (sz.L n) (sz.lam n) E) δ

theorem unDensBARow'_holds : UNDensBARow'
```

### Check-file equality (compiled)
Scratch file = `docs/tickets/checks/T2300-check.lean` with `import RBM3D.BA.MReg` added after `import RBM3D.BA.UNPins` and these lines appended; `lake env lean`, exit 0, no output:
```lean
/-! ## 4. Equality of the compiled theorems with the pinned statements -/
namespace RBM.BA.T2300Check
example : BAm_sub_le_of_im_pin := @RBM.BA.BAm_sub_le_of_im
example : BAbulk_window_pin := @RBM.BA.BAbulk_window
example : BArho_lip_of_bulk_pin := @RBM.BA.BArho_lip_of_bulk
example : BArho_rate_of_bulk_pin := @RBM.BA.BArho_rate_of_bulk
example : BAm_im_lower_window_pin := @RBM.BA.BAm_im_lower_window
example : unDens'_ba_pin := @RBM.Univ.unDens'_ba
example : unDensBARow'_holds_pin := RBM.Univ.unDensBARow'_holds
```

### Compiled nonempty instances (namespace `RBM.BA.MRegInst`, file lines 346-384; part of the `lake build` above)
```lean

/-- `κ = (Im m_S)/π > 0` at the merged flow point. -/
private theorem MReg_flow_pos : 0 < (mS 4 10).im / Real.pi := div_pos (selfS 4 10).1 Real.pi_pos

/-- The `ρ`-bulk datum of the flow point, as in `RBM.BA.ImmLowerInst` (I4). -/
private theorem MReg_flow_bulk : BAbulk 3 4 g0P ((mS 4 10).im / Real.pi) EP := by
  unfold BAbulk BArho
  rw [BAm_real_eq_of_self 3 4 g0P EP m0P flowP_real.1]
  exact div_le_div_of_nonneg_right flowP_real.2 Real.pi_pos.le

/-- (I1) The pin `UNDensBARow'` itself. -/
example : UNDensBARow' := unDensBARow'_holds

/-- (I2) Target 2 at the flow point: the window `|x - E_P| ≤ (πκ)³/8` stays in the `κ/2`-bulk. -/
example : ∀ x : ℝ, |x - EP| ≤ (Real.pi * ((mS 4 10).im / Real.pi)) ^ 3 / 8 →
    BAbulk 3 4 g0P ((mS 4 10).im / Real.pi / 2) x :=
  fun x hx => BAbulk_window 3 4 g0P _ EP x MReg_flow_pos MReg_flow_bulk hx

/-- (I3) Target 5 at the flow point. -/
example : ∀ x η : ℝ, |x - EP| ≤ (Real.pi * ((mS 4 10).im / Real.pi)) ^ 3 / 8 → 0 < η → η ≤ 10 →
    (Real.pi * ((mS 4 10).im / Real.pi)) ^ 5 / 2048 ≤
      (BAm 3 4 g0P ((x : ℂ) + (η : ℂ) * Complex.I)).im :=
  fun x η hx h0 h10 => BAm_im_lower_window 3 4 g0P _ EP x η MReg_flow_pos MReg_flow_bulk hx h0 h10

/-- (I4) Target 6 at the merged class sequence `S0` (the coupling parameter of `S0` is the private
`UNPins_hg_3_10`, hence the existential form; proof irrelevance identifies `by norm_num : 0 < 3/10` with it). -/
example : ∃ E κ : ℝ, 0 < κ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (Real.pi * κ) ^ 3 / 8 →
    UNDens' (fun n => BAm 3 ((RBM.Univ.BAInst.S0 : Sizes 3).L n) ((RBM.Univ.BAInst.S0 : Sizes 3).lam n)) E
      (fun n => BArho 3 ((RBM.Univ.BAInst.S0 : Sizes 3).L n) ((RBM.Univ.BAInst.S0 : Sizes 3).lam n) E) δ :=
  have hg : (0 : ℝ) < 3 / 10 := by norm_num
  ⟨(RBM.BA.UNPinsInst.fp 4 hg).E, RBM.BA.UNPinsInst.clsκ 4 hg, RBM.BA.UNPinsInst.clsκ_pos 4 hg,
    fun δ hδ hδ' => unDens'_ba 3 RBM.Univ.BAInst.S0 _ _ (RBM.BA.UNPinsInst.clsκ_pos 4 hg)
      RBM.Univ.BAInst.S0_bulk δ hδ hδ'⟩

/-- (I5) The merged consumer with `rD` discharged by the proved pin. -/
example (rT : UNTrLocalInitBARow') (rN : UNNormBARow) (hLoc : UNLocAvgBA) :=
  RBM.Univ.BAInst.inst_step1GoodC''_ba unDensBARow'_holds rT rN hLoc

end RBM.BA.MRegInst
```

### Registry pre-check and full build
Full `lake build` on the branch as committed (root `RBM3D.lean` does not import `RBM3D.BA.MReg`; the hub adds that import at merge):
```
error: RBM3D.lean:342:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`, `refutedProps`, `supersededProps`:
  [RBM.Univ.UNDensBARow']
Classify each of them: borrowed from the literature, owed by this formalization, a predicate that defines the objects under study, refuted (shown false and superseded), or superseded (not needed).
```
So the root import and the registry deletion must land together. With a temporary, uncommitted line `import RBM3D.BA.MReg` after `import RBM3D.Induction.QEndA` in `RBM3D.lean` (removed again; `git status` shows only the two committed files), the full build:
```
$ lake build 2>&1 | tail -3
non-vacuity certificates: 0 of 146 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4107 jobs).
lake build  42.81s user 6.46s system 86% cpu 57.155 total
```
Pre-check file (`import RBM3D`, `import RBM3D.BA.MReg`, `#assert_rbm_axioms`; `lake env lean`, exit 0):
```
$ head -1 precheck.out
axiom audit: 8632 theorems, 2823 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ tail -1 precheck.out
non-vacuity certificates: 0 of 146 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
$ grep -c "UNDensBARow'" precheck.out
0
```
`UNDensBARow'` appears neither in the owed ledger nor in the unregistered list of the audit output.

### Name-clash grep (`grep -rl` over `RBM3D/`, `RBM3D.lean` excluding `RBM3D/BA/MReg.lean`; and `docs/tickets/T*.md` excluding T2300)
```
BAm_sub_le_of_im: main-tree files 0, tickets 0
BAbulk_window: main-tree files 0, tickets 0
BArho_lip_of_bulk: main-tree files 0, tickets 0
BArho_rate_of_bulk: main-tree files 0, tickets 0
BAm_im_lower_window: main-tree files 0, tickets 0
unDens'_ba: main-tree files 0, tickets 0
unDensBARow'_holds: main-tree files 0, tickets 0
MRegInst: main-tree files 0, tickets 0
MReg_: main-tree files 0, tickets 0
```

### Ports
No port from RBM1D/RBM2D: nothing copied, no RBM1D/RBM2D diff-stat applies. In-repo template: `RBM3D/BA/Boundary.lean:244-279` (subsequence step `tendsto_subseq_of_bounded`, `BASelf_of_tendsto`), `RBM3D/BA/ImmLower.lean:456-468` (flow-point bulk datum), `RBM3D/Universality/PinsDens.lean:175-215` read only.

### Narrative
- All seven targets are proved unconditionally in `RBM3D/BA/MReg.lean` (384 lines; the ticket's cap is 1500, estimate 300/500/800). Targets 1-5 are in `RBM.BA`, 6-7 in `RBM.Univ`, private helpers have the prefix `MReg_`; no new public definition.
- Routes as in the ticket (R1)-(R7). Target 1 and the two-point lemma `MReg_two` use `BASelf_sub_le` (`ImmLower.lean:252`); target 2 uses `η_k = (πκ)³/(8(k+1))`, `tendsto_subseq_of_bounded` and `BASelf_of_tendsto` (`Boundary.lean:164`); target 5 uses `BAm_im_lower_of_bulk` for `η ≤ 1` and `BAm_im_ge_mul` with `κ₁ ≤ 1` for `1 < η ≤ 10`; target 6 uses `BArho_rate_of_bulk` and `squeeze_zero'` for the `𝓝[>] 0` limit, not `BArho_tendsto`.
- Target 4: `m(E + iη)` has no lower bound `κ₁`, so the estimate is `κ₁² ‖m_E - m'‖ ≤ 2η` (sum `Im m_E² + Im m'² ≥ κ₁²`), as in (a) row 6; the same for target 2 (row 3).
- Constants of `unDens'_ba`, fixed before `∀ᶠ n`: `c = (πκ)⁵/2048`, `C = K = 1`, `Lp = 1/c²`; window `δ ≤ (πκ)³/8`; pin `δ₀ = (πκ)³/8`.
- Premises of `UNDensBARow'` not used by the proof: `3 ≤ d`, `sz.Admissible 𝔠 𝔡` (so `𝔠`, `𝔡`); `3 ≤ L` only through the instance `Sizes.neZeroL`. Targets 1-6 assume no sign of `g = λ_n`.
- Instance (I4) states `∃ E κ`, witnesses `(fp 4 hg).E`, `clsκ 4 hg` with `hg : (0:ℝ) < 3/10 := by norm_num`; the merged `S0` is built from the private `UNPins_hg_3_10`, and proof irrelevance identifies the two proofs (the example compiles). (I5) is `inst_step1GoodC''_ba` with `rD := unDensBARow'_holds`, with `rT`, `rN`, `hLoc` as hypotheses of the example (other gates' owed pins, CLAUDE.md §4 step 2).
- The numeric check (viii) was not rerun: the preflight's run is in (a) (one instance at `d = 3`, `L = 4`, `g = 3/10`, `E = 0`), and every inequality it tests is now a compiled theorem.
- Registry: the owed line `RBM.Univ.UNDensBARow'` was deleted from `RBM3D/Test/Axioms.lean` (one line removed); no new line; the pre-check flagged nothing else.
- Build warnings in `MReg.lean`: only `linter.style.longLine` on the module docstring (the `set_option` is after the docstring, as in `ImmLower.lean`).

## (c) Verified Mathlib names (`#check` in `lake env lean`, exit 0)
- `tendsto_subseq_of_bounded`: bounded set, `x n ∈ s` gives `∃ a ∈ closure s, ∃ φ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a)`.
- `Metric.isBounded_closedBall`, `mem_closedBall_zero_iff : a ∈ closedBall 0 r ↔ ‖a‖ ≤ r`.
- `Complex.abs_im_le_norm : |z.im| ≤ ‖z‖`, `Complex.im_le_norm : z.im ≤ ‖z‖`, `Complex.re_add_im : ↑z.re + ↑z.im * I = z`, `Complex.continuous_im`, `Complex.norm_real`.
- `tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ) : Tendsto (fun n => 1 / (↑n + 1)) atTop (𝓝 0)`.
- `squeeze_zero'` (`0 ≤ f` and `f ≤ g` eventually, `g → 0`), `tendsto_iff_dist_tendsto_zero`, `nhdsWithin_le_nhds`, `self_mem_nhdsWithin`, `ge_of_tendsto`.
- `pow_le_pow_of_le_one : 0 ≤ a → a ≤ 1 → m ≤ n → a ^ n ≤ a ^ m`; `div_le_div_iff₀ : 0 < b → 0 < d → (a / b ≤ c / d ↔ a * d ≤ c * b)`; `le_div_iff₀`; `div_le_one`; `sub_add_cancel_left : a - (a + b) = -b`.
- Names verified absent: none searched.

## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none new. The uniform-in-`n` Lipschitz form `UNDens'` versus the paper's "continuous density" (`1_2:624`) is the structural form registered at `docs/paper-deltas.md:1471` (D512, T2201c: `UNDens'` structural; "T2201a、b：Lean 结构，无陈述差异", i.e. Lean structure, no statement differences).
- Hub at merge: `import RBM3D.BA.MReg` must be added to `RBM3D.lean` before the full `lake build` (see the first block of "Registry pre-check"), because the registry deletion makes `UNDensBARow'` count as proved only once `BA/MReg` is in the import closure of the root.
- Plan row update at merge (`docs/reports/T2173-portmap.md:274`) is the dispatcher's: BA-C2 depends on BA-D2, D3 (Ward), D6, D7 and BA-C1b, not D4; delivered size 384 lines.
- The docstring of `UNDensBARow'` (`UNPins.lean:153-158`) names the route `unDens'_freeConvST` (as did the deleted registry comment); superseded by (R6) here (merged text, not edited, §57 (1)).
- No obstruction; no target weakened; no hypothesis added; no frozen signature touched.

