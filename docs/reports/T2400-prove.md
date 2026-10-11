Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct 11 00:38:25 UTC 2026

Notation: `M = M^{(B)} = BAMB d L g E m` (translation invariant, symmetric), `M^{++}_{ab} = M_{ba} M_{ab} = M_{ab}^2` (`BAMss … true true`), `ε = κ²/4`, `|x| = zdistD d L x`, `c₀ = BAct_rate d Λ κ`, `μ = BAp5s_rate d Λ κ`, `S_c := expC (d-2) c` (`Σ_x e^{-c|y-x|} ≤ S_c`, uniform in `L`, `BAsum_exp_decay_le`, needs `2 ≤ d`). Common hypotheses of all targets: `2 ≤ d` (the paper's `3 ≤ d` is used only as `2 ≤ d`), `3 ≤ L`, `0 < Λ`, `0 < g ≤ Λ`, `0 < κ`, `BAReal d L g κ E m` (= `BASelf d L g E m ∧ κ ≤ Im m`), `0 ≤ t ≤ 1`. (S1) needs only `0 < κ`, `BAReal`, `0 ≤ t ≤ 1`: no `g ≤ Λ`, no `Λ`, no `3 ≤ L`.

### (i) Exponent table

| Quantity | Value / formula | Constraint | Slack (script rows A, B below) |
|---|---|---|---|
| `ε` | `κ²/4` | `ε ≤ |1 - t m²|` (`BAoffDiag_scalar`, `t ∈ [0,1]`); `1-|m|² ≤ (1-ε)|1-t m²|` | A: `ε = 1/16`, B: `ε = 4.84e-4`; both `0 < ε` |
| `K` of (S1) | `1/ε² = 16 κ⁻⁴` | max principle at the maximiser `a` of `|v|`: `|1-tm²| V - t(1-|m|²) V ≤ B` (diag `m²` by `BAMss_ss_diag`; off-diag row sum `1-|m|²` by `BAMss_row_offdiag_sum`); `t(1-|m|²) ≤ 1-|m|² ≤ (1-ε)|1-tm²|` gives `ε|1-tm²| V ≤ B`, then `|1-tm²| ≥ ε` gives `V ≤ B/ε²` | A: `K = 256`, actual `max_t ‖Θ_t‖_{∞→∞} = 1`; B: `K = 4.269e6`, actual `4.334`. `K` has no `g`, no `Λ`, no `L` |
| `c₀` | `min(log(1+κ/(4dΛ)), κ/2)` | `> 0` (`BAct_rate_pos`) | A: `0.04082`; B: `3.666e-4` |
| `ν` | `c₀/2` | `0 < ν < c₀`: leftover rate `c₀ - ν = c₀/2 > 0` | slack `c₀/2` |
| `ρ` (`ρ_B`: `sup_c Σ_b |M_bc|`; same for rows by `BAMB_symm`) | `≤ c₀⁻¹ S_{c₀}` (`BAMB_row_l1`; fine lattice `BAMfine_row_l1`) | uniform in `L`, `W` | A: `1.101 ≤ 5.42e10`; B: `4.653 ≤ 9.28e20` |
| `ρ₂` | `sup_{a,c} Σ_b |M_ab||M_bc| ≤ 1` | Cauchy–Schwarz + `Σ_b|M_ab|² = 1` (`BAMB_ward_row` at real `E`, i.e. `BAMB_row_sq_real`) and `Σ_b|M_bc|² = Σ_b|M_cb|² = 1` (`BAMB_symm`) | A, B: `1.000 ≤ 1` (equality up to rounding: slack 0) |
| `ρ̂` | `Σ_b |M_ab| e^{ν|a-b|} ≤ c₀⁻¹ S_{c₀/2}` | `|M_ab| ≤ c₀⁻¹ e^{-c₀|a-b|}` (`BAMB_decay_large`; fine lattice `BAMfine_decay`, block distance `[x]-[y]`), times `e^{c₀|a-b|/2}`, then `BAsum_exp_decay_le` with `c = c₀/2 > 0` | A: `1.103 ≤ 8.67e11`; B: `4.656 ≤ 1.49e22` |
| `C₅`, `μ` | `C₅ = 2/ε² + 2AS/ε³`, `A = 4(C/c₀)²`, `C = 16d²/κ³`, `S = S_{c₀}`; `μ = min(c₀, ε²c₀/(2AΛ²S))` (`BAp5s_C`, `BAp5s_rate`) | `μ ≤ c₀`, `μ > 0` | A: `μ = 1.131e-23 ≤ c₀`; B: `μ = 1.484e-50 ≤ c₀` |
| `c_λ` | `min(c₀/12, μ/6)` | `2c_λ ≤ μ/3`, so `μ - 2c_λ ≥ 2μ/3 > 0`; `c_λ ≤ c₀/12 < c₀/2` | A: `c_λ = 1.885e-24 = μ/6`; B: `2.474e-51 = μ/6`; slack in `μ-2c_λ ≥ 2μ/3`: `μ/3` (checked True) |
| `C_Θ̂` | `C₅(1 + Λ² S_{2μ/3})` | `sup_b Σ_{a'} |Θ_{t,ba'}| e^{2c_λ|b-a'|} ≤ C_Θ̂`: shift `Θ_{t,ba'} = Θ_{t,0,a'-b}` (`baP8_BATheta_shift`), `‖Θ_{t,0x}‖ ≤ C₅(1_{x=0} + g² e^{-μ|x|})` (`baProp5s_of_real`, explicit `C₅, μ`, any `σ`, `t ∈ [0,1]`), `e^{2c_λ|x|-μ|x|} ≤ e^{-(2μ/3)|x|}`, `g² ≤ Λ²`, `BAsum_exp_decay_le` with `c = 2μ/3` | A: `1 ≤ 1.096e119`; B: `4.334 ≤ 3.27e253` |

Choice (translation invariance of `Θ`): **make `baP8_BATheta_shift` (`BA/Prop6Path.lean:497`) public in place** (delete the word `private`; name, signature and proof unchanged). Evidence it is safe, from `grep` on `main`/worktree `d859e60`: the name occurs only in `Prop6Path.lean` (lines 497, 1008, 1025, 1160, 1172) and a docstring mention in `EKPins.lean:288`; `Prop6Path` is imported only by `BA/KInduct`, `BA/KStep`, `BA/EKPins`, and `RBM3D.lean`; its proof uses `private lemma baP8_BAMss_shift` (`:483`), which may stay private since the public proof only refers to it. Restating in `GreenStab` is not chosen (duplicates a 25-line proof).

Statement of (S1) against the body of the probe's `BAStab` (`t/T2390:RBM3D/Probe/T2390Pins.lean:44-47`, extracted by `git show … | sed -n 44,47p`):
```
def BAStab (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (t K : ℝ) : Prop :=
  ∀ (v : Zd d L → ℂ) (B : ℝ),
    (∀ a, ‖v a - (t : ℂ) * ∑ b, BAMss d L (BAMB d L g (E : ℂ) m) true true a b * v b‖ ≤ B) →
      ∀ a, ‖v a‖ ≤ K * B
```
`baStab_of_real d L g κ E m (hκ : 0 < κ) (hr : BAReal d L g κ E m) t (ht0 : 0 ≤ t) (ht1 : t ≤ 1)` has the conclusion `∀ (v : Zd d L → ℂ) (B : ℝ), (hypothesis line 3 above, verbatim) → ∀ a, ‖v a‖ ≤ 16 * κ⁻¹ ^ 4 * B`, i.e. the lines `∀ (v…) (B…)`, the `(∀ a, …≤ B) →` line, and `∀ a, ‖v a‖ ≤ K * B` with `K := 16 * κ⁻¹ ^ 4` and the first line replaced by the extra hypotheses; `BAStab d L g E m t (16 * κ⁻¹ ^ 4)` is then `fun v B h a => baStab_of_real … v B h a` (`K * B` unfolds by beta, `16 * κ⁻¹ ^ 4 * B`). `K = 16κ⁻⁴ = 1/ε²` exactly (`ε = κ²/4`). `BAStab` itself is not defined in this ticket.

Other targets in mathematics: (S3) `ρ₂`: `∀ a c, Σ_b ‖M_ab‖‖M_bc‖ ≤ 1`; `ρ` column form `∀ c, Σ_b ‖M_bc‖ ≤ c₀⁻¹ S_{c₀}` (by `BAMB_symm` from `BAMB_row_l1`, `d = k+2`); `ρ̂` block form `∀ a, Σ_b ‖M_ab‖ e^{(c₀/2)|a-b|} ≤ c₀⁻¹ S_{c₀/2}` and, on the fine lattice, `∀ x, Σ_y ‖M^{fine}_{xy}‖ e^{(c₀/2)|[x]-[y]|} ≤ c₀⁻¹ S_{c₀/2}` (fibre sum over the offset: `BAMfine_eq`; the merged `GreenSchur_fibre_sum` is private, so a private copy is needed). (S2) `sup_b Σ_{a'} ‖Θ_{t,σσ,ba'}‖ e^{2c_λ|b-a'|} ≤ C_Θ̂`, all `σ`, `t ∈ [0,1]`. Note: the ticket cites `baProp5s_holds`, which only gives `∃ C c`; the explicit `C₅ = BAp5s_C`, `μ = BAp5s_rate` needed in `C_Θ̂` come from `baProp5s_of_real` (`Prop5Short.lean:608`; theorem with explicit constants, `0 ≤ t ≤ 1`), which `baProp5s_holds` itself applies.

### (ii) One concrete nondegenerate instance

Lean data: `d = 3`, `L = 4` (`sz0_values.1`), flow datum `n = 0` of `sz0`: `g_I = BAflowLam0 sz0 zSeq 0 ∈ (0, 1/64]` (`EKPins.lean:652,656`), `κ = 1/2`, `BAReal 3 (sz0.L 0) g_I (1/2) E_I m_I` is `EKPins.lean:668` (`hrI := BAflow_real … flow_sz0 0`, merged, so no external hypothesis; no `g ≤ Λ` issue: `Λ = 1`, `g_I ≤ 1/64 ≤ 1`), `t = 1/2 ∈ [0,1]`, `σ` any, `Λ = 1`. `v = δ_0` (nonzero), `B = 3/2`: `|v_a - ½ M_{a0}²| ≤ 1 + ½` since `|M_{a0}|² ≤ Σ_b|M_ab|² = 1`; conclusion `|v_a| ≤ 256 · 3/2 = 384`, and `v_0 = 1`. No `N = 0`, no empty index (`card Zd 3 4 = 64`), no collapsed window.

Numerical check of every hypothesis and bound at actual matrices (`Ψ` = adjacency of `Z_4^3`, `M = (gΨ - E - m)⁻¹`, `m` from the fixed point iteration `m = 64⁻¹ tr M`). Row A has `g = 1/64`, `E = 0` (representative of the flow datum; the true `E_I` is not computed), `Λ = 1`, `κ = 1/2`. Row B is the stress data of CONTROL G2 (supervisor 2254): `Λ = 10`, `g = 10`, `κ = 0.044 ≤ Im m = 0.098` (the value 0.044 is the supervisor's figure; the script only verifies `κ ≤ Im m` at `E = 1.1`):

`python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/60e5425b-ae97-4201-b2dc-fc981af93073/scratchpad/T2400/final.py`
```
[A: Lean-instance data] d=3 L=4 g=0.015625 E=0.0 Lam=1.0 kappa=0.5 Im m=0.999269 t in [0, 0.25, 0.5, 0.75, 1.0]
  BASelf resid 1.11e-16 | Ward max dev 1.332e-15 | diag M++ - m^2 1.554e-15 | offdiag row sum - (1-|m|^2) 2.93e-16
  (S1) max_t ||Theta_t||_inf->inf = 1 <= K=16/kappa^4 = 256
  (S3) rho 1.101 <= 5.42e+10 | rho2 1 <= 1 | rhohat 1.103 <= 8.672e+11
  (S2) sup_b sum_a |Theta_ba| e^{2cl|b-a|} 1 <= C_Thhat 1.096e+119
  consts c0 0.04082 mu 1.131e-23 cl 1.885e-24 C5 5.774e+22 S_{c0} 2.212e+09 mu<=c0 True cl<=mu/6 True mu-2cl>=2mu/3 True
[B: G2 data] d=3 L=4 g=10 E=1.1 Lam=10.0 kappa=0.044 Im m=0.098077 t in [0, 0.25, 0.5, 0.75, 0.9, 1.0]
  BASelf resid 9.55e-16 | Ward max dev 9.326e-15 | diag M++ - m^2 1.438e-15 | offdiag row sum - (1-|m|^2) 9.215e-15
  (S1) max_t ||Theta_t||_inf->inf = 4.334 <= K=16/kappa^4 = 4.269e+06
  (S3) rho 4.653 <= 9.279e+20 | rho2 1 <= 1 | rhohat 4.656 <= 1.485e+22
  (S2) sup_b sum_a |Theta_ba| e^{2cl|b-a|} 4.334 <= C_Thhat 3.271e+253
  consts c0 0.0003666 mu 1.484e-50 cl 2.474e-51 C5 5.103e+47 S_{c0} 3.402e+17 mu<=c0 True cl<=mu/6 True mu-2cl>=2mu/3 True
```
(The script asserts `3 ≤ L`, `0 < g ≤ Λ`, `0 < κ ≤ Im m`, `0 ≤ t ≤ 1`, `|m| ≤ 1`, and `‖Θ_t‖_{∞→∞} ≤ 4/(κ²|1-tm²|)` for every `t` tested.)

External hypotheses: none. All inputs (`baProp5s_of_real`, `BAMB_decay_large`, `BAMB_row_sq_real`, `BAoffDiag_scalar`, `BAflow_real`, `flow_sz0`) are merged theorems; no limit computation is needed.

### Verdicts

- (S1) `baStab_of_real`: PASS (argument re-derived above; constant `16κ⁻⁴ = 1/ε²`; hypotheses all hold at rows A, B).
- (S3) row facts `ρ`, `ρ₂`, `ρ̂`: PASS.
- (S2) `Θ` facts (public shift; weighted `ℓ¹` row bound with `C_Θ̂`): PASS, with the correction that `baProp5s_of_real` (not `baProp5s_holds`) supplies the explicit `C₅`, `μ`.

(a′) Preflight corrections: none; (a) stands.

## (b) Script output — Sun Oct 11 00:55:52 UTC 2026; stage 1b (ticket role `prover-hard`, model claude-sonnet-5-5), worktree `../RBM3D-wt/T2400`, branch `t/T2400`
Line count against the stop line (1,000): `GreenStab.lean` 442 lines (first command) plus the net diff of `Prop6Path.lean` 0 (one line replaced: the `git diff -U0` block). `$SCR` = the scratchpad dir `T2400/` of this session.
$ wc -l RBM3D/BA/GreenStab.lean   # stop line 1000 = this + net diff of Prop6Path.lean (the git diff -U0 block below: 1 line in, 1 line out)
     442 RBM3D/BA/GreenStab.lean
$ lake build RBM3D.BA.GreenStab 2>&1 | tail -n 1
Build completed successfully (3756 jobs).
$ lake build 2>&1 | tail -n 1   # whole library, runs #assert_rbm_axioms
Build completed successfully (4210 jobs).
$ lake env lean $SCR/axioms.lean 2>&1 | python3 -I $SCR/axsum.py   # #print axioms of all new public decls + baP8_BATheta_shift
21 declarations, each depends on exactly [propext, Classical.choice, Quot.sound]; other lines: []
baStab_of_real baM_row_l1 baM_col_l1 baM_rho2 baM_rhohat baMfine_rhohat GreenStab_clam GreenStab_CTheta GreenStab_clam_pos GreenStab_clam_le_c0 GreenStab_clam_le_mu baTheta_weighted_l1 baP8_BATheta_shift GreenStabInst.hr0I GreenStabInst.inst_baStab GreenStabInst.inst_col_l1 GreenStabInst.inst_rho2 GreenStabInst.inst_rhohat GreenStabInst.inst_rhohat_fine GreenStabInst.inst_theta_weighted GreenStabInst.inst_theta_shift
$ grep -cE "sorry|admit|native_decide|^axiom|^ *axiom " RBM3D/BA/GreenStab.lean
0
$ python3 -I $SCR/stmts.py RBM3D/BA/GreenStab.lean baStab_of_real baM_row_l1 baM_col_l1 baM_rho2 baM_rhohat baMfine_rhohat GreenStab_clam GreenStab_CTheta baTheta_weighted_l1
GreenStab.lean:46 theorem baStab_of_real (d L : ℕ) [NeZero L] (g κ E : ℝ) (m : ℂ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ∀ (v : Zd d L → ℂ) (B : ℝ), (∀ a, ‖v a - (t : ℂ) * ∑ b, BAMss d L (BAMB d L g (E : ℂ) m) true true a b * v b‖ ≤ B) → ∀ a, ‖v a‖ ≤ 16 * κ⁻¹ ^ 4 * B
GreenStab.lean:116 theorem baM_row_l1 (hd : 2 ≤ d) (hL : 3 ≤ L) (Λ g κ E : ℝ) (m : ℂ) (hΛ : 0 < Λ) (hg : 0 < g) (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (a : Zd d L) : ∑ b, ‖BAMB d L g (E : ℂ) m a b‖ ≤ (BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ)
GreenStab.lean:123 theorem baM_col_l1 (hd : 2 ≤ d) (hL : 3 ≤ L) (Λ g κ E : ℝ) (m : ℂ) (hΛ : 0 < Λ) (hg : 0 < g) (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (c : Zd d L) : ∑ b, ‖BAMB d L g (E : ℂ) m b c‖ ≤ (BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ)
GreenStab.lean:132 theorem baM_rho2 (g E : ℝ) (m : ℂ) (h : BASelf d L g (E : ℂ) m) (a c : Zd d L) : ∑ b, ‖BAMB d L g (E : ℂ) m a b‖ * ‖BAMB d L g (E : ℂ) m b c‖ ≤ 1
GreenStab.lean:147 theorem baM_rhohat (hd : 2 ≤ d) (hL : 3 ≤ L) (Λ g κ E : ℝ) (m : ℂ) (hΛ : 0 < Λ) (hg : 0 < g) (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (a : Zd d L) : ∑ b, ‖BAMB d L g (E : ℂ) m a b‖ * Real.exp (BAct_rate d Λ κ / 2 * (zdistD d L (a - b) : ℝ)) ≤ (BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ / 2)
GreenStab.lean:188 theorem baMfine_rhohat (d : ℕ) (hd : 2 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (hL : 3 ≤ sz.L n) (hg : 0 < lam0 n) (hgΛ : lam0 n ≤ Λ) (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) (x : Idx d (sz.L n) (sz.W n)) : ∑ y : Idx d (sz.L n) (sz.W n), ‖BAMfine sz lam0 E n x y‖ * Real.exp (BAct_rate d Λ κ / 2 * (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) x).1 - (split d (sz.L n) (sz.W n) y).1) : ℝ)) ≤ (BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ / 2)
GreenStab.lean:221 def GreenStab_clam (d : ℕ) (Λ κ : ℝ) : ℝ := min (BAct_rate d Λ κ / 12) (BAp5s_rate d Λ κ / 6)
GreenStab.lean:224 def GreenStab_CTheta (d : ℕ) (Λ κ : ℝ) : ℝ := BAp5s_C d Λ κ * (1 + Λ ^ 2 * expC (d - 2) (2 * BAp5s_rate d Λ κ / 3))
GreenStab.lean:251 theorem baTheta_weighted_l1 (hd : 2 ≤ d) (hL : 3 ≤ L) (Λ g κ E : ℝ) (m : ℂ) (hΛ : 0 < Λ) (hg : 0 < g) (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (σ : Bool) (b : Zd d L) : ∑ a', ‖BATheta d L g E m t σ σ b a'‖ * Real.exp (2 * GreenStab_clam d Λ κ * (zdistD d L (b - a') : ℝ)) ≤ GreenStab_CTheta d Λ κ
$ python3 -I $SCR/cmp.py   # probe t/T2390:RBM3D/Probe/T2390Pins.lean:44-47 (BAStab body) vs baStab_of_real conclusion
probe body : ∀ (v : Zd d L → ℂ) (B : ℝ), (∀ a, ‖v a - (t : ℂ) * ∑ b, BAMss d L (BAMB d L g (E : ℂ) m) true true a b * v b‖ ≤ B) → ∀ a, ‖v a‖ ≤ K * B
K := 16 * κ⁻¹ ^ 4 substituted in probe body: True
conclusion : ∀ (v : Zd d L → ℂ) (B : ℝ), (∀ a, ‖v a - (t : ℂ) * ∑ b, BAMss d L (BAMB d L g (E : ℂ) m) true true a b * v b‖ ≤ B) → ∀ a, ‖v a‖ ≤ 16 * κ⁻¹ ^ 4 * B
$ lake env lean $SCR/link.lean; echo "exit $?"   # scratch: BAStab copied from the probe; theorem link : BAStab d L g E m t (16 * κ⁻¹ ^ 4) := fun v B h a => baStab_of_real d L g κ E m hκ hr t ht0 ht1 v B h a
exit 0
$ lake env lean docs/tickets/checks/T2400-check.lean > /dev/null; echo "exit $?"
exit 0
$ python3 -I $SCR/stmts.py RBM3D/BA/GreenStab.lean hr0I inst_baStab inst_col_l1 inst_rho2 inst_rhohat inst_rhohat_fine inst_theta_weighted inst_theta_shift   # namespace GreenStabInst
GreenStab.lean:352 theorem hr0I : BAReal 3 (sz0.L 0) g0I (1 / 2) E0I m0I
GreenStab.lean:371 theorem inst_baStab : vI 0 = 1 ∧ ∀ a, ‖vI a‖ ≤ 16 * (1 / 2 : ℝ)⁻¹ ^ 4 * (3 / 2)
GreenStab.lean:397 theorem inst_col_l1 : ∑ b, ‖BAMB 3 (sz0.L 0) g0I (E0I : ℂ) m0I b 0‖ ≤ (BAct_rate 3 1 (1 / 2))⁻¹ * expC (3 - 2) (BAct_rate 3 1 (1 / 2))
GreenStab.lean:404 theorem inst_rho2 : ∑ b, ‖BAMB 3 (sz0.L 0) g0I (E0I : ℂ) m0I 0 b‖ * ‖BAMB 3 (sz0.L 0) g0I (E0I : ℂ) m0I b 0‖ ≤ 1
GreenStab.lean:409 theorem inst_rhohat : ∑ b, ‖BAMB 3 (sz0.L 0) g0I (E0I : ℂ) m0I 0 b‖ * Real.exp (BAct_rate 3 1 (1 / 2) / 2 * (zdistD 3 (sz0.L 0) (0 - b) : ℝ)) ≤ (BAct_rate 3 1 (1 / 2))⁻¹ * expC (3 - 2) (BAct_rate 3 1 (1 / 2) / 2)
GreenStab.lean:417 theorem inst_rhohat_fine : ∑ y : Idx 3 (sz0.L 0) (sz0.W 0), ‖BAMfine sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0 0 y‖ * Real.exp (BAct_rate 3 1 (1 / 2) / 2 * (zdistD 3 (sz0.L 0) ((split 3 (sz0.L 0) (sz0.W 0) 0).1 - (split 3 (sz0.L 0) (sz0.W 0) y).1) : ℝ)) ≤ (BAct_rate 3 1 (1 / 2))⁻¹ * expC (3 - 2) (BAct_rate 3 1 (1 / 2) / 2)
GreenStab.lean:427 theorem inst_theta_weighted : ∑ a', ‖BATheta 3 (sz0.L 0) g0I E0I m0I (1 / 2) true true 0 a'‖ * Real.exp (2 * GreenStab_clam 3 1 (1 / 2) * (zdistD 3 (sz0.L 0) (0 - a') : ℝ)) ≤ GreenStab_CTheta 3 1 (1 / 2)
GreenStab.lean:435 theorem inst_theta_shift (a b r : Zd 3 (sz0.L 0)) : BATheta 3 (sz0.L 0) g0I E0I m0I (1 / 2) true true (a + r) (b + r) = BATheta 3 (sz0.L 0) g0I E0I m0I (1 / 2) true true a b
$ grep -rnE '(theorem|def|lemma|abbrev) (baStab_of_real|baM_row_l1|baM_col_l1|baM_rho2|baM_rhohat|baMfine_rhohat|baTheta_weighted_l1|GreenStab_[A-Za-z0-9_]*|g0I|E0I|m0I|hr0I|vI|vI_zero|Q_le_one|inst_baStab|inst_col_l1|inst_rho2|inst_rhohat|inst_rhohat_fine|inst_theta_weighted|inst_theta_shift)\b' RBM3D RBM3D.lean --include='*.lean' | grep -v 'BA/GreenStab.lean' | wc -l; git grep -c 'GreenStab\|baStab_of_real' main -- RBM3D RBM3D.lean | wc -l
       0
       0
$ git diff -U0 main...t/T2400 -- RBM3D/BA/Prop6Path.lean RBM3D.lean | grep "^[-+][^-+]"
+import RBM3D.BA.GreenStab
-private lemma baP8_BATheta_shift (g E : ℝ) (m : ℂ) (t : ℝ) (σ₁ σ₂ : Bool) (a b r : Zd d L) :
+lemma baP8_BATheta_shift (g E : ℝ) (m : ℂ) (t : ℝ) (σ₁ σ₂ : Bool) (a b r : Zd d L) :
$ git diff --stat main...t/T2400 | cat; git log --format="%h %s" main..t/T2400
 RBM3D.lean              |   1 +
 RBM3D/BA/GreenStab.lean | 442 ++++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/BA/Prop6Path.lean |   2 +-
 3 files changed, 444 insertions(+), 1 deletion(-)
8403a83 T2400: docstring citations
49c1978 T2400: BA stability bound (S1), M row facts (S3), Theta weighted l1 row (S2), instances

## (c) Verified Mathlib names (`#check` in this worktree; every other name used is witnessed by the successful build)
$ lake env lean $SCR/names2.lean 2>&1 | python3 -I $SCR/chk.py
@Finite.exists_max ... inst : LinearOrder β] (f : α → β), ∃ x₀, ∀ (x : α), f x ≤ f x₀
@Finset.sum_mul_sq_le_sq_mul_sq ...  i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2
@Finset.add_sum_erase ...  M) {a : ι}, a ∈ s → f a + ∑ x ∈ s.erase a, f x = ∑ x ∈ s, f x
@Fintype.sum_equiv ...  (g : κ → M), (∀ (x : ι), f x = g (e x)) → ∑ x, f x = ∑ x, g x
@Finset.sum_ite_eq' ... (∑ x ∈ s, if x = a then b x else 0) = if a ∈ s then b a else 0
@add_le_add_left ... : LE α] [i : AddRightMono α], b ≤ c → ∀ (a : α), b + a ≤ c + a
@pow_le_pow_left₀ ... M₀] [MulPosMono M₀], 0 ≤ a → a ≤ b → ∀ (n : ℕ), a ^ n ≤ b ^ n 
Finding for `docs/mathlib-api.md`: in this Mathlib `add_le_add_left : b ≤ c → ∀ a, b + a ≤ c + a` (summand `a` on the right); `add_le_add le_rfl h` was used instead. Names verified absent: none searched.

## (d) Narrative, open issues, paper-delta candidates
- Choice (ii): `baP8_BATheta_shift` made public in place (the word `private` deleted at `Prop6Path.lean:497`; name, signature, proof unchanged; `baP8_BAMss_shift` stays private).
- Routes: (S1) at a maximiser of `|v|` as in (a), constant `1/ε² = 16 κ⁻⁴`; `baM_rho2` Cauchy-Schwarz with `BAMB_row_sq_real`, `BAMB_symm`; `baM_rhohat` `BAMB_decay_large` times `e^{(c₀/2)r}` then `BAsum_exp_decay_le`; the fine form through `BAMfine_eq` and a private copy of the fibre sum; `baTheta_weighted_l1` by the shift reindexing, `baProp5s_of_real` (explicit `C₅`, `μ`, as noted in (a)), `6 c_λ ≤ μ`, `BAsum_exp_decay_le` at `2μ/3`, `g² ≤ Λ²`.
- `BAStab` is not defined here; the link `fun v B h a => baStab_of_real …` compiled only in the uncommitted scratch file (output above).
- Added beyond the ticket text (stem-prefixed, CLAUDE.md §3 (E)): `GreenStab_clam`, `GreenStab_CTheta`, `GreenStab_clam_pos`, `_le_c0`, `_le_mu`; `baM_row_l1` (general `2 ≤ d`, the merged `BAMB_row_l1` is `d = k + 2`). `ρ` on the fine lattice is the merged `BAMfine_row_l1` (not re-proved); no fine-lattice column bound was proved.
- `baM_rho2` is stated under `BASelf` (weaker than `BAReal` in the (a) hypothesis line; `hr.1` supplies it); no `κ`, `Λ`, `L ≥ 3` is used.
- Instances: `hr0I` is the merged `BAflow_real` at `flow_sz0` (`κ = 1/2`), `g0I ∈ (0, 1/64]`, `Λ = 1`, `t = 1/2`, `L = 4`; `inst_baStab` uses the nonzero `vI = δ_0`, `B = 3/2` (hypothesis proved from Ward); every deterministic hypothesis is discharged, none left open.
- Copies within RBM3D (no RBM1D/RBM2D port, so no diff-stat): `GreenSchur_fibre_sum` (`BA/GreenSchur.lean:161`), `gI_pos`, `gI_le` (`BA/EKPins.lean:652,656`).
- Open for the hub: the branch contains the one `import RBM3D.BA.GreenStab` line in `RBM3D.lean` (the ticket lists `RBM3D.lean` as writable; CLAUDE.md §3 (A) step 4 has the hub add it): do not add a second line.
- Paper-delta candidates: `T2400a` (S1): `K = 16 κ⁻⁴ = ε⁻²`, `ε = κ²/4`, from `BAoffDiag_scalar` and the max principle (not in the paper: `A_deterministic_estimates.tex:28-41` uses the Neumann series `eq:expMLn` for the entry decay (5s); `T2390k` records the `BAStab` shape); `T2400b`: explicit `c_λ = min(c₀/12, μ/6)`, `C_Θ̂ = C₅(1 + Λ² S_{2μ/3})`, `ρ̂ = c₀⁻¹ S_{c₀/2}` (T2390 (a′) D3.4); `T2400c`: `3 ≤ d` used as `2 ≤ d` (as in `baProp5s_of_real`).
