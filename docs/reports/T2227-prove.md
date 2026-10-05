Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 23:38:34 UTC 2026

All statements below are the compiled T2205 probe texts (96e4087, `RBM3D/Probe/T2205Pins.lean`), read from `git show`; `BAmWindow_holds` constants read at probe `:1124-1157`, `BAwindow_step` at `:884-1120`. "Derived" = checked by hand here from those proof lines, not claimed by the ticket.

### (i) Exponent table (`d = 3`; Lean needs only `1 ≤ d` in the proofs, `3 ≤ d` is a premise of `BAmWindow`/`BAWinBulk_of_dom_stmt`)

| # | Quantity | Value | Constraint it must satisfy | Slack |
|---|---|---|---|---|
| 1 | step bound `δ = g - g'` of `BAwindow_step` | `δ ≤ κ⁹/(64d)` | `r := 2dδ/κ⁴ ≤ κ⁵/32` (probe `:hr5`) | `0` at `δ = κ⁹/(64d)` (equality by construction); instance: `r = 3.8557e-05 = κ⁵/32` (script 1) |
| 2 | ball radius `r` vs `Im m = b ≥ κ` | `r ≤ κ⁵/32` | `r ≤ b/2` (keeps `|Im w_i| ≥ b/2`, `‖w⁻¹‖ ≤ 2/b`) | `κ⁵/32 ≤ κ/2` iff `κ⁴ ≤ 16`; `κ ≤ b ≤ 1` (`BAself_im_le_one`) gives factor ≥ 16; instance `r = 3.9e-5 ≤ b/2 = 0.2803` |
| 3 | `θ = 2dδ + r` (change of `w_i = gλ_i-E-μ` between `(g,m)` and `(g',μ)`, `‖μ-m‖ ≤ r`) | `θ ≤ 2r` (`2dδ = rκ⁴ ≤ r`) | `θ ≤ b⁵/16` (probe `:hθ5`) | `2r ≤ κ⁵/16 ≤ b⁵/16`: slack `0` at `b = κ`, `δ` maximal; factor `(b/κ)⁵` otherwise |
| 4 | contraction factor `q` of `T(μ) = μ - F_{g'}(μ)/A` on `B(m,r)` | `q = 1/2` | `‖A_diff‖ ≤ 2θ(2/b)³ = 16θ/b³ ≤ b² ≤ ‖A‖/2` (gap `‖A‖ ≥ Re A ≥ 2b²`, `BAgapReal_holds`) | `16θ/b³ ≤ b²` iff `θ ≤ b⁵/16`: row 3 (slack 0 at the extreme) |
| 5 | self-map: `‖T(m) - m‖ ≤ r/2` | `‖F_{g'}(m)‖ ≤ 2dδ/b² ` (`|λ_i| ≤ 2d`, `‖w⁻¹‖ ≤ 1/b`), `/‖A‖ ≥ 2b²` gives `dδ/b⁴ ≤ r/2` | `q r + r/2 ≤ r` | `0` (`q = 1/2`); fixed point = `BAm d L g' E` by `BAm_real_eq_of_self` |
| 6 | `|λ_i| ≤ 2d` (spectrum of `PsiB`, `Adj` = `ℓ¹`-distance 1, `card_adj = 2d`, `L ≥ 3`) | `max|λ_i| = 6 = 2d` at `d = 3, L = 4` (script 1) | `|λ_i| ≤ 2d` | `0` (attained: `λ = 2d` for the constant vector) |
| 7 | window constant `c₁` | `min(1/2, κ⁹/(64dΛ))` | `0 < c₁ ≤ 1/2`; `(1-√(1-c₁)) g ≤ c₁ Λ ≤ κ⁹/(64d)` (`g ≤ Λ`) | `1 - √(1-c₁) ≤ c₁` for `c₁ ≤ 1` (since `1-c₁ ≤ √(1-c₁)`); instance `c₁ = 3.03e-09`, needed `g0(1-√(1-c₁)) = 7.07e-09 ≤ κ⁹/(64d) = 3.03e-08`: factor 4.3 |
| 8 | Lipschitz constant `C` | `2d/κ⁴` | `‖m(E,g') - m‖ ≤ C(g - g')` (= row 5 radius) | instance `C = 1273.95`; observed max ratio `7.14e-4` (script 1), `0.945` at the second point (script 2) |
| 9 | gap `Re(1 - L⁻ᵈ tr M²) ≥ 2(Im m)²` | `⟨|w|⁻²⟩ = 1` (imag. part of `(self_m)`), `Re(1-⟨w⁻²⟩) = 2b²⟨|w|⁻⁴⟩ ≥ 2b²` (Cauchy-Schwarz) | gap used in row 4 | instance `1.988 ≥ 0.629` (factor 3.2); second point `0.558 ≥ 0.152` |
| 10 | bulk loss `κ ↦ κ/2` | `Im m(E,g') ≥ b - r ≥ κ - κ⁵/32 ≥ κ/2` | `≥ κ/2` | `κ⁵/32 ≤ κ/32` against `κ/2`: factor 16 |
| 11 | `BAzztE_inv`: `0 < τ < 1`, `z' = (E + (1-τ)m₀)/√τ` | `Im z' = (1-τ) Im m₀/√τ > 0` | `Im z' ≥ 0` for `BASelf_unique` (`BAm_real_eq_of_self`-type uniqueness); `BAt0(z', √τ m₀) = τ`, `BAflowE = E` | exact identities (derived: `BAt0 = √τ b/(√τ b + (1-τ)b/√τ) = τ`; `BAflowE`: the `Re m₀` terms cancel); residuals `0`, `2e-31` (script 1) |
| 12 | `BAWinBulk_of_dom_stmt`: `BAdom` at `κ`, `0 < lam n ≤ Λ` | `κ ≤ Im m(z,g)`, `N^{-1+ε} ≤ Im z ≤ 1`; `BAdom_real` gives `κ ≤ Im m₀ = Im m/√t₀`, `g₀ = √t₀ g ≤ g ≤ Λ` | premises of `BAmWindow` at `(g₀, E, m₀)` | instance: `κ = Im m_S = 0.2620`, `Im m₀ = 0.5607`, `g₀ = 4.672 ≤ Λ = 10`, `N^{-1+ε} = 0.00364 ≤ Im z_S = 0.938 ≤ 1` |

Sizes: `Sizes.size n = (W L)^d` (`RBM3D/Defs/Sizes.lean:157`); `L = 4, W = 2, d = 3` gives `512`.

### (ii) One concrete nondegenerate instance
`d = 3`, `L ≡ 4` (`card Zd 3 4 = 64`), `W ≡ 2` (`N = 512`), `lam ≡ g = Λ = 10`, `w = 6i/5`, `m_S = L⁻ᵈ tr(gΨ - w)⁻¹`, `z_S = w - m_S`, `κ = Im m_S`, `t₀ = Im m_S/(Im m_S + Im z_S)`, `E`, `m₀ = m_S/√t₀`, `g₀ = √t₀ g`; `ε = 1/10`; `τ = t₀`. Hypotheses of every target at once: `BAmWindow` (`3 ≤ d`, `0 < Λ`, `0 < κ`, `3 ≤ L`, `0 < g0 ≤ Λ`, `BAReal d L g0 κ E m0`); `BAzztE_inv` (`0 < g`, `0 < τ < 1`, `BASelf d L (√τ g) E m0`); `BAgapReal` (`BASelf d L g0 E m0`); `BAWinBulk_of_dom_stmt` (`0 < lam ≤ Λ`, `BAdom` at `z_S`). The one-point `BAWinBulk` window lies in the `κ/2`-bulk. Script (Python, mathematics only; the eigenvalues of `Ψ` are built from `Adj` = `ℓ¹`-distance 1 on `Z_4^3`):

`cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2227 && python3 inst.py`:
```text
card Zd = 64 = L^d = 64 ; degree = 6 = 2d; max|lambda_i| = 5.999999999999998 <= 2d = 6
m_S = (4.601354020028481e-16+0.26196878337926194j)  z_S = (-4.601354020028481e-16+0.9380312166207381j)  Im z_S in (0,1]: True
BASelf residual (m_S) = 0.0  Im m_S>0: True
t0 = 0.21830731948271828  E = -9.848078456772e-16  m0 = (9.848078456772001e-16+0.560680425960381j)  g0 = 4.672336883003175  0<t0<1: True  g0<=Lam: True
BASelf(g0,E,m0) residual = 3.330691404284494e-16  BAReal: kappa <= Im m0: True
z' = (-4.601354020028478e-16+0.9380312166207381j)  m(z',10) = (4.601354020028481e-16+0.26196878337926194j)  sqrt(t0)*m0 = (4.601354020028481e-16+0.26196878337926194j)  |diff| = 0.0
BAt0(z', sqrt(t0) m0) - t0 = 0.0  BAflowE(...) - E = 1.9721522630525295e-31
Re(1 - L^-d tr M^2) = 1.9881897381174907  >= 2 (Im m0)^2 = 0.6287250801102287 : True ; <|w|^-2> = 0.9999999999999997
kappa = Im m_S = 0.26196878337926194  c1 = min(1/2, k^9/(64 d Lam)) = 3.026527747174518e-09  C = 2d/k^4 = 1273.9520373561552
1-sqrt(1-c1) <= c1: True ; (g0-g'_min) = 7.070478488686006e-09  <= k^9/(64d) = 3.0265277471745185e-08
r = 2 d delta/k^4 = 3.855651189627912e-05  <= k^5/32 = 3.855651189627912e-05  <= b/2 = 0.2803402129801905
window grid: min Im m(E,g') = 0.5606804259603808  >= kappa/2 = 0.13098439168963097 : True ; max |m-m0|/(g0-g') = 0.0007140401450079121  <= C: True
size N = (W L)^d = 512 ; N^(-1+eps) = 0.0036446601231906535  <= Im z_S = 0.9380312166207381  <= 1: True ; Im m(z_S,g) = Im m_S = 0.26196878337926194 >= kappa_dom: True
0 < lam = 10 <= Lam = 10: True; 3 <= d, 3 <= L: True
```

`cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2227 && python3 inst2.py` (second, asymmetric point `d = 3, L = 5` (odd `L`, `E = 0.7 ≠ 0`), all three pins tested at once; `τ = 0.81`):
```text
card Zd = 125 = L^d = 125 ; degree = 6 = 2d; max|lambda_i| = 5.999999999999999 <= 2d = 6
second point d=3 L=5 g=1.3 E=0.7: m = (0.20661795772386204+0.2759273794879766j)  Im m = 0.2759273794879766  residual 1.2412670766236366e-16
gap Re(1-avg w^-2) = 0.5580992083908597  >= 2(Im m)^2 = 0.15227183750220366 : True
zztE_inv: |m(z',g)-sqrt(tau) m0| = 1.2412670766236366e-16  t0'-tau = 0.0
window: kappa = 0.2759273794879766  c1(Lean) = 3.7145703410149885e-08  C = 1035.0755849425548  sweep g' in [g/sqrt2,g]: min Im m = 0.2759273794879767 >= kappa/2 = 0.1379636897439883 True  max Lip = 0.9445473170533245 <= C: True
```
External hypothesis: none (T2227 uses no external input; all hypotheses are merged `BA` or order relations, DECISIONS §72 (3)). The limit-type facts used (`N^{-1+ε} → 0`) enter only as the finite instance value `0.00364 ≤ Im z_S` above.

### (iii)-(vi) Pins against the paper, §29, two data one model, consumers, registry
Paper `paper/tex/7_8_light_weight.tex:1790-1832` (read): `zztE_BA` `:1796-1808` with `t₀ = Im m/(Im m + Im z)`, `E = (t₀ Re z - (1-t₀) Re m)/√t₀`, `g₀ = √t₀ g`, `√t₀ m(E,g₀) = m(z,g)`, `z_{t₀}(E,g₀) = √t₀ z`; `:1813` is commented out (`%In other words ... z_t stays within the bulk ... provided t ≥ 1 - ε ...`).

| Pin | what it says | paper | §29 (1)-(7) | two data, one model | class / consumer |
|---|---|---|---|---|---|
| `BAgapReal` | `2(Im m)² ≤ Re(1 - L⁻ᵈ tr M²)` for `BASelf` at `(g,E)` real | not in the paper (D537 = T2205c; row 9 proves it) PASS | (1) no `s,t`; (2) no gate; (3) `3 ≤ L`, no `L`-`W`, `d` free; (4) `∀ L g E m` pointwise; (5) none; (6) `0 < g`; (7) none | `Im m → 0⁺`: gap `→ 0`, outside `BASelf` (`0 < Im m`) PASS | proved `BAgapReal_holds`; used by `BAwindow_step` |
| `BAmWindow Λ κ` | `∃ c₁ ∈ (0,1/2], C`: for `g ≤ Λ`, `BAReal κ`, `g' ∈ [√(1-c₁)g, g]`: `BAReal (κ/2)` at `BAm g'`, Lipschitz `C(g-g')` | not in paper (D537; continuous form commented `:1813`) PASS | (1) none; (2) none; (3) `3 ≤ d` premise, proofs use `1 ≤ d`, `3 ≤ L` binder; (4) `c₁, C` after `κ, Λ`, before `L g E m`; (5) none; (6) `0 < Λ, κ, g`; (7) `κ ↦ κ/2` | uniform: only `|λ_i| ≤ 2d`, `Im m ≤ 1` used (rows 5-6) PASS | proved `BAmWindow_holds`; hypothesis only of `BAWinBulk_of_dom` |
| `BAzztE_inv` | `(τ,E,m₀)` with `BASelf (√τ g) E m₀` ⇒ `BAm g z' = √τ m₀`, `BAt0 = τ`, `BAflowE = E`, `z' = z_τ/√τ` | inverse of `zztE_BA` `:1796-1808`: `z_{t₀} = √t₀ z` rewritten (row 11) PASS | (1) `0 < τ < 1` premises; (2) none; (3) `3 ≤ L`; (4) pointwise; (5) none; (6) `0 < g, τ`; (7) none | `z'` determined by `(m₀,E,τ)`; `BAm` unique on `Im z' ≥ 0` (`BAm_real_eq_of_self`) PASS | proved `BAzztE_inv_holds`, core `BAzztE_inv_core`; consumer BA-S3 |
| `BAWinBulk` (written out with merged `BAt0`, `BAm`, `BAflowE`) | window `[√(1-c₁)g₀, g₀]` in `κ`-bulk at every `n` | structural (§51 `Im m ≥ κ`) PASS | `∀ n g'`; no `ε`, `L`-`W` | values below the window not observed (window is a hypothesis) PASS | structural (portmap P.2): `structuralProps` if flagged; conclusion only here |
| `BAWinBulk_of_dom_stmt d` | `3 ≤ d → ∀ κ Λ >0, ∃ c₁ ∈ (0,1/2], ∀ ε sz z, (0 < lam n ≤ Λ) → BAdom κ ε (z n) → BAWinBulk sz z c₁ (κ/2)` | §51 chain domain `Im m ≥ κ`; D538 `∀ n, 0 < lam n`; PASS | (3) `3 ≤ d` (`3 ≤ L` by `sz.three_le_L`); (4) `∀ n` premises pointwise, `c₁` after `κ, Λ` before `ε sz z`, conclusion `∀ n`; (5) none; (6) `0 < κ, Λ, lam n`; (7) loss `κ ↦ κ/2` taken by consumers (T2205 audit O5) | uniform in `n` (`BAmWindow` constants depend on `κ, Λ, d` only) PASS | proved `BAWinBulk_of_dom_holds`; consumers BA-V3, BA-M1, BA-S3 |

Consumer check (§45 O2): the probe consumers are applications only (script 3: no `unfold`/`simp`/`rw`/`change` line mentions `BAWinBulk` in the probe), so T2197-named probe text accepts the written-out `BAWinBulk` (`rfl`-equal, probe `:3974`). Registry plan (Targets 3): no line expected; `BAWinBulk` would go to `structuralProps` if the pre-check flags it.

### (vii) Script 3 (blocks from `git show 96e4087:RBM3D/Probe/T2205Pins.lean` saved as `probe.txt` in the same directory; name clash)
```text
blocks lines: [44, 149, 73, 483, 6, 7, 26, 31, 17, 23] total 859
33 names + CouplingWindowInst; declaration hits in RBM3D/ outside Probe/: 0
probe lines with unfold/simp/rw/dsimp/change mentioning BAWinBulk: []
```

### Verdicts
- Target 1 (copy B1-B10, 859 probe lines, (c1)-(c6)): PASS (mathematics: rows 1-12 close; slack 0 in rows 1, 3, 4 is by construction of `κ⁹/(64d)` and does not fail any inequality).
- Target 2 (imports `RBM3D.BA.MFixedPoint`, `Mathlib.Topology.MetricSpace.Contracting`): PASS (no mathematics).
- Target 3 (registry, no line expected): PASS.
- Pins `BAgapReal`, `BAmWindow`, `BAzztE_inv`, `BAWinBulk`, `BAWinBulk_of_dom_stmt`: PASS each; no `T2227a` candidate (D537/D538 cited, not re-proposed).
- Instance: nondegenerate (`N = 512`, `card Zd = 64`, `κ = 0.262`, `c₁ = 3.0e-09 > 0`, window width `g0(1-√(1-c₁)) = 7.1e-09 > 0`); the window is narrow because `c₁ ~ κ⁹` (T2205 (a′), T2205 audit O4: valid, conservative).

## (b) Script output — Mon Oct  5 23:42:29 UTC 2026

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2227`, branch `t/T2227`, commit 3e769f1 (base 0f44a56); `git diff --stat main...t/T2227`:
```text
 RBM3D/BA/CouplingWindow.lean | 921 +++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 921 insertions(+)
```

`lake build RBM3D.BA.CouplingWindow` (tail; lines containing "error": 0, "warning:" lines: 14: long-line hints in the new module docstring and flexible-`simp`/`show` style hints in the moved text):
```text
modifies the current goal, which was modified by the flexible tactic `simp` on line 473!
Build completed successfully (3334 jobs).
exit 0
```

Full `lake build` in the worktree (root `RBM3D.lean` is not changed by this ticket, so it does not import the new module; the hub adds the import and runs the full build at merge):
```text
Build completed successfully (4030 jobs).
```

Registry pre-check (`import RBM3D` + `import RBM3D.BA.CouplingWindow` + `#assert_rbm_axioms`, `lake env lean`; head 3 lines of output; `grep -n "BAgapReal\|BAmWindow\|BAzztE_inv\|BAWinBulk\|CouplingWindow"` of the full output: no match, so no name flagged; no `RBM3D/Test/Axioms.lean` change):
```text
axiom audit: 6623 theorems, 2260 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
exit 0
```

Axioms (`#print axioms`, scratch file importing the module):
```text
'RBM.BA.BAMB_trace_sq_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAgapReal_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAzztE_inv_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAzztE_inv_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAm_im_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAself_im_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAwindow_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAmWindow_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAwindow_iter' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAwindow_floor' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAWinBulk_of_dom' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAWinBulk_of_dom_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.CouplingWindowInst.BAm_zP' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.CouplingWindowInst.flowP_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.CouplingWindowInst.g0P_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.CouplingWindowInst.g0P_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.CouplingWindowInst.flowP_real' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`/`admit`/`native_decide`/`axiom` in the file (`grep -n "sorry\|admit\|native_decide\|^axiom"`: 0 lines).

Target statements, extracted from the file by script (heads up to `:=`; the three pin bodies are compared to the check file below):
```text
-- L55
def BAgapReal : Prop :=
-- L66
def BAmWindow (Λ κ : ℝ) : Prop :=
-- L76
def BAzztE_inv : Prop :=
-- L799
def BAWinBulk (sz : Sizes d) (z : ℕ → ℂ) (c₁ κ : ℝ) : Prop :=
-- L807
def BAWinBulk_of_dom_stmt (d : ℕ) : Prop :=
-- L130
theorem BAMB_trace_sq_eq_sum (d L : ℕ) [NeZero L] : ∀ (g : ℝ) (z m : ℂ), (z + m).im ≠ 0 →
    (BAMB d L g z m * BAMB d L g z m).trace = ∑ i, (((BAspec d L g i : ℂ) - (z + m))⁻¹) ^ 2
-- L159
theorem BAgapReal_holds (d : ℕ) : BAgapReal d
-- L239
theorem BAzztE_inv_core (d L : ℕ) [NeZero L] (g τ E : ℝ) (m₀ : ℂ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hself : BASelf d L (Real.sqrt τ * g) (E : ℂ) m₀) :
    BAm d L g (ztOf m₀ E τ / (Real.sqrt τ : ℂ)) = (Real.sqrt τ : ℂ) * m₀ ∧
      BAt0 (ztOf m₀ E τ / (Real.sqrt τ : ℂ)) ((Real.sqrt τ : ℂ) * m₀) = τ ∧
        BAflowE (ztOf m₀ E τ / (Real.sqrt τ : ℂ)) ((Real.sqrt τ : ℂ) * m₀) = E
-- L303
theorem BAzztE_inv_holds (d : ℕ) : BAzztE_inv d
-- L320
theorem BAm_im_nonneg {d L : ℕ} [NeZero L] {g : ℝ} {z : ℂ} : 0 ≤ (BAm d L g z).im
-- L328
theorem BAself_im_le_one {d L : ℕ} [NeZero L] {g : ℝ} {z m : ℂ} (hz : 0 ≤ z.im) (h : BASelf d L g z m) : m.im ≤ 1
-- L448
theorem BAwindow_step (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (hd : 1 ≤ d) {g g' E κ : ℝ} (hκ : 0 < κ) (hg : 0 < g)
    {m : ℂ} (hm : BASelf d L g (E : ℂ) m) (hκm : κ ≤ m.im) (hg' : g' ≤ g) (hδ : g - g' ≤ κ ^ 9 / (64 * d)) :
    ∃ m' : ℂ, BASelf d L g' (E : ℂ) m' ∧ ‖m' - m‖ ≤ 2 * d * (g - g') / κ ^ 4 ∧ κ / 2 ≤ m'.im
-- L688
theorem BAmWindow_holds (d : ℕ) (Λ κ : ℝ) : BAmWindow d Λ κ
-- L723
theorem BAwindow_iter (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (hd : 1 ≤ d) {E κf : ℝ} (hκf : 0 < κf) :
    ∀ (N : ℕ) {g g' : ℝ}, 0 < g' → g' ≤ g → g - g' ≤ N * (κf ^ 9 / (64 * d)) →
      ∀ {m : ℂ}, BASelf d L g (E : ℂ) m → κf + 2 * d * (g - g') / κf ^ 4 ≤ m.im →
        ∃ m' : ℂ, BASelf d L g' (E : ℂ) m' ∧ ‖m' - m‖ ≤ 2 * d * (g - g') / κf ^ 4 ∧ κf ≤ m'.im
-- L778
theorem BAwindow_floor (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (hd : 1 ≤ d) {g g' E κ κf : ℝ} (hκf : 0 < κf)
    (hg' : 0 < g') (hle : g' ≤ g) {m : ℂ} (hm : BASelf d L g (E : ℂ) m) (hκm : κ ≤ m.im)
    (hbudget : κf + 2 * d * (g - g') / κf ^ 4 ≤ κ) :
    κf ≤ (BAm d L g' (E : ℂ)).im ∧ ‖BAm d L g' (E : ℂ) - m‖ ≤ 2 * d * (g - g') / κf ^ 4
-- L817
theorem BAWinBulk_of_dom (d : ℕ) (hw : ∀ Λ κ : ℝ, BAmWindow d Λ κ) : BAWinBulk_of_dom_stmt d
-- L836
theorem BAWinBulk_of_dom_holds (d : ℕ) : BAWinBulk_of_dom_stmt d := BAWinBulk_of_dom d (BAmWindow_holds d)```

Verbatim check (`python3 verb.py`; each of B1-B10 from `git show 96e4087:RBM3D/Probe/T2205Pins.lean`, with (c1) applied to B2 and `private ` inserted at the four lines of B4 (c2), is a contiguous block of the file, in order; (c3) body byte-equal to `T2205-check.lean:173-176`):
```text
B1 44 True
B2 149 True
B3 73 True
B4 483 True
B5 6 True
B6 7 True
B7 26 True
B8 31 True
B9 17 True
B10 23 True
c3 body byte-equal: True
ordered: True
```
Diff of the file against the concatenated (transformed) blocks: `diff concat.txt CouplingWindow.lean | grep -c "^<"` = 0 removed lines; added lines = 63 (copyright/imports/module docstring, probe `:31-43` header lines, `namespace`/`end` lines, blank separators, the 4-line (c3) body, the 2-line (c6) replacement).

Check-file equality (scratch = `T2227-check.lean` + `import RBM3D.BA.CouplingWindow` + 17 `example`s: `rfl` for `BAgapReal`, `BAzztE_inv`, `BAWinBulk_of_dom_stmt`, `@BAmWindow`, `@BAWinBulk d`; `T2227Check.Y_pin := @RBM.BA.Y` for the 12 public theorems):
```text
examples in scratch: 17; lake env lean eq.lean: exit 0, lines containing "error": 0
```

The compiled nonempty instances (the four `examples` of `RBM.BA.CouplingWindowInst`, lines 884-911 of the file; `d = 3`, `L = 4`, `N = 512`, no hypothesis left open; the two lines `have e` / `rw [e] at hlo hhi ⊢` are (c6)):
```lean
/-- **The window at the flow point of `(L, g) = (4, 10)`** (`BAmWindow_holds`; no hypothesis): the chain pins' window premise
`BAWinBulk` holds for the one-point sequence `L ≡ 4`, `lam ≡ 10`, `z ≡ z_S(4, 10)` (flow data `(g₀, E) = (g0P, EP)`), with some
`c₁ > 0` (the proof's `c₁ = min(1/2, κ⁹/(64 d Λ))`, `κ = Im m_S(4, 10)`), and `Im m ≥ κ/2` on the window. -/
example :
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 / 2 ∧ BAWinBulk szP zP c₁ ((mS 4 10).im / 2) := by
  obtain ⟨c₁, h0, h1, C, hC, H⟩ := BAmWindow_holds 3 10 (mS 4 10).im (by norm_num) (by norm_num) (selfS 4 10).1
  refine ⟨c₁, h0, h1, fun n g' hlo hhi => ?_⟩
  have e : BAm 3 (szP.L n) (szP.lam n) (zP n) = mS 4 10 := BAm_zP
  rw [e] at hlo hhi ⊢
  exact (H 4 (by norm_num) g0P g0P_pos g0P_le EP m0P flowP_real g' hlo hhi).1.2

/-- `BAzztE_inv` at these data: the inverse of `zztE_BA` returns `m(z', 10) = √t₀ m₀`, horizon `t₀`, energy `E`. -/
example : BAm 3 4 10 (ztOf m0P EP t0P / (Real.sqrt t0P : ℂ)) = (Real.sqrt t0P : ℂ) * m0P ∧
    BAt0 (ztOf m0P EP t0P / (Real.sqrt t0P : ℂ)) ((Real.sqrt t0P : ℂ) * m0P) = t0P ∧
      BAflowE (ztOf m0P EP t0P / (Real.sqrt t0P : ℂ)) ((Real.sqrt t0P : ℂ) * m0P) = EP :=
  BAzztE_inv_holds 3 4 (by norm_num) 10 (by norm_num) t0P EP m0P flowP_data.1 flowP_data.2.1 flowP_data.2.2

/-- `BAgapReal` at the real-axis data of the flow point: `Re (1 - 4^{-3} tr M²) ≥ 2 (Im m₀)²` at `L = 4`, `g₀ = g0P`. -/
example : 2 * m0P.im ^ 2 ≤
    (1 - (((4 ^ 3 : ℕ) : ℂ))⁻¹ * (BAMB 3 4 g0P (EP : ℂ) m0P * BAMB 3 4 g0P (EP : ℂ) m0P).trace).re :=
  BAgapReal_holds 3 4 (by norm_num) g0P g0P_pos EP m0P flowP_data.2.2

/-- The spectral form of `M²` at the same data. -/
example : (BAMB 3 4 g0P (EP : ℂ) m0P * BAMB 3 4 g0P (EP : ℂ) m0P).trace =
    ∑ i, (((BAspec 3 4 g0P i : ℂ) - ((EP : ℂ) + m0P))⁻¹) ^ 2 :=
  BAMB_trace_sq_eq_sum 3 4 g0P (EP : ℂ) m0P (by
    have := flowP_data.2.2.1
    simp only [Complex.add_im, Complex.ofReal_im, zero_add]
    exact this.ne')
```

Name clash (`grep -rnE "(theorem|lemma|def|abbrev|structure|instance|namespace) (private )?(<name>)( |$)" RBM3D --include=*.lean`, excluding the new file, for the 33 declared names and `CouplingWindowInst`; run in the worktree (base 0f44a56) for all 34 names; in the main worktree (37289f6) for a 14-name subset (all five defs, `BAwindow_*`, `szP`, `zP`, `t0P`, `g0P`, `flowP_real`, `CouplingWindowInst`)): 0 hits. Dependency check: the file builds with only the two imports of Targets 2 (no import added); `grep -n "Probe\|BAflowLam0\|BAflowEs\|BAflowT0" RBM3D/BA/CouplingWindow.lean`:
```text
13:Port of the compiled T2205 probe (`RBM3D/Probe/T2205Pins.lean` at `96e4087`, sections 2, 2.1-2.3, 3.2 and the
21:* the window premise `BAWinBulk` (written out with the merged `BAt0`, `BAm`, `BAflowE`, because `BAflowT0`, `BAflowEs`, `BAflowLam0`
```

Ports: from the probe (`RBM3D/Probe/T2205Pins.lean` on `t/T2205` at 96e4087), no RBM1D/RBM2D port in this ticket (no RBM1D/RBM2D diff-stat applicable).

## Narrative (b)

- The file is the concatenation of the probe blocks B1-B10 (859 probe lines) with the changes (c1)-(c6) of the ticket and the header; the only proof lines I wrote are the two (c6) lines of the window example (`have e`, `rw [e] at hlo hhi ⊢`); they compiled at the first attempt.
- (c1) docstring of `T2205_inv_spectral` changed as specified (private copy kept); (c2) all four helpers (`abs_eigenvalue_le`, `BASelf_iff_fixed`, `inv_mul_inv_sub_le`, `norm_inv_le_of_abs_im`) compiled as `private`.
- (c3): the written-out `BAWinBulk` body is byte-equal to `T2205-check.lean:173-176`; `BAWinBulk_of_dom` (B7) compiled unchanged; `T2227Check.BAWinBulk = BAWinBulk` by `rfl`.
- Imports exactly `RBM3D.BA.MFixedPoint` and `Mathlib.Topology.MetricSpace.Contracting`; no import added.
- `RBM3D/BA/MFixedPoint.lean` and `RBM3D.lean` are untouched; the root import and the full `lake build` with the module are the hub's merge step.
- The module docstring is new text (not in the probe); the long-line hints come from it, since the probe's `set_option linter.style.longLine false` follows the docstring.
- The `T2227Check.*_pin` statements are accepted by `@RBM.BA.Y` for the 12 public theorems (17 `rfl`/term examples, exit 0).

## (c) Verified Mathlib names

Proof-only Mathlib names are those of the probe blocks (T2205 report section (c)); this ticket added none and checked none newly; the module compiles with the imports above, which is the verification. No name verified absent.

## (d) Open issues and paper-delta candidates

- No open issue. No `T2227a` candidate (no pin differs from its paper line beyond D537 = T2205c and D538 = T2205d, which are cited, not re-proposed).
- Registry: the pre-check flagged no name; no `RBM3D/Test/Axioms.lean` line.
- Observation for BA-S3: the probe text it ports writes `BAWinBulk` arguments with T2197's `BAflowLam0`/`BAflowEs`; here `BAWinBulk` is the written-out form (`rfl`-equal).
