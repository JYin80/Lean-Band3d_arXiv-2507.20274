Prover model: claude-sonnet-5-5
## (a) Math preflight — Tue Oct  6 11:51:59 UTC 2026

### (i) Exponent table
Notation: `N = L^d`, `v_i = BAspec d L g i`, `a_i = (v_i - (z+m))⁻¹`, `b_i = (v_i - (z'+m'))⁻¹`, `T = ⟨a b⟩`, `⟨f⟩ = N⁻¹ Σ_i f_i`.
All constants below were re-derived by hand from the route of the ticket (M0–M5); no external hypothesis occurs (every step is finite algebra over `Zd d L`).

| constant | value | constraint it must satisfy | slack |
|---|---|---|---|
| `c` of the pin `BAImmLower` | `κ⁵/64` | `c > 0`; depends on `κ` only, chosen before `L, g, E, m` | `> 0` since `κ > 0` |
| `κ ≤ 1` | derived | `κ ≤ Im m ≤ ‖m‖ ≤ 1` (`BAReal`; `BAm_norm_le_one`, `Ward.lean:136`) | needed in M3 (`κ⁵ ≤ κ`) and M4 (`κ+η+2 ≤ η+3`) |
| `⟨\|a\|²⟩` | `Im m/(Im z + Im m) ≤ 1`, `= 1` at real `z` | Ward identity `Im m = (Im z + Im m)⟨\|a\|²⟩` (needs `Im z ≥ 0`, `Im m > 0`) | exact |
| `\|T\|` (M2) | `≤ ⟨\|a\|\|b\|⟩ ≤ (⟨\|a\|²⟩+⟨\|b\|²⟩)/2 ≤ 1` | needs `Im z, Im z' ≥ 0` | exact bound 1 |
| `Re(1-T)` (M2) | `≥ (Im m² + Im m'²)/2` | `Im a_i, Im b_i > 0`; `⟨Re a²⟩ ≤ 1 - Im m²` (Jensen `⟨Im a⟩ = Im m`) | exact |
| Lipschitz const. of target 1 | `(Im m² + Im m'²)‖m-m'‖ ≤ 2‖z-z'‖` | `‖1-T‖ ≥ Re(1-T)`, `(m-m')(1-T) = (z-z')T` | const. 2 (the merged real-axis `BAgapReal` has 1 at `z=z'`) |
| threshold of target 2 | `η ≤ η₀ := κ³/4` | `κ²‖m-m'‖ ≤ 2η ≤ κ³/2` | `‖m-m'‖ ≤ κ/2`, `Im m' ≥ κ/2` |
| branch 1 (`η ≤ κ³/4`) | `Im m' ≥ κ/2` | must be `≥ κ⁵/64` | ratio `(κ/2)/(κ⁵/64) = 32/κ⁴ ≥ 32` |
| `δ` of target 3 | `δ = ‖(E+iη+m') - (E+m)‖ ≤ η + ‖m‖ + ‖m'‖ ≤ η+2` | `‖m‖,‖m'‖ ≤ 1` (`BAm_norm_le_one`) | `κ + δ ≤ η + 3` since `κ ≤ 1` |
| `\|a_i\|` | `≤ 1/Im m ≤ 1/κ` | `\|Im(v_i - E - m)\| = Im m ≥ κ` | used in `\|b_i\| ≥ \|a_i\|κ/(κ+δ)` |
| target 3 | `Im m' ≥ ηκ²/(η+3)²` (every `η > 0`) | `⟨\|b\|²⟩ ≥ κ²/(κ+δ)² ≥ κ²/(η+3)²`; `Im m' = (η+Im m')⟨\|b\|²⟩ ≥ η⟨\|b\|²⟩` | exact |
| branch 2 (`κ³/4 < η ≤ 1`) | `(η+3)² ≤ 16`, `Im m' ≥ ηκ²/16` | must be `≥ κ⁵/64` | `ηκ²/16 > κ⁵/64` strictly (`η > κ³/4`); at `η = 1`: ratio `4/κ³ ≥ 4` |
| target 6 constant | `(πκ)⁵/64` | `BAbulk κ ⇔ ∃ m, BASelf E m ∧ πκ ≤ Im m` (`BAbulk_iff_exists`, `MFixedPoint.lean:830`); then target 4 at `πκ` | `πκ > 0` |
| unused pin premises | `3 ≤ d`, `0 < Λ`, `0 < g`, `g ≤ Λ`; `3 ≤ L` only via `NeZero L` | none of the six statements needs them | listed for the report |

Junction: for `η ≤ κ³/4` branch 1 gives `Im m' ≥ κ/2 ≥ 32·κ⁵/64`; for `κ³/4 < η ≤ 1` branch 2 gives `Im m' ≥ ηκ²/16 > κ⁵/64`; the two ranges cover `(0, 1]`.
Algebra: `a_i - b_i = a_i b_i((z+m) - (z'+m'))` (since `1/w - 1/w' = (w'-w)/(w w')`, `w = v_i-(z+m)`); averaging gives `m-m' = T((z-z')+(m-m'))`, i.e. `(m-m')(1-T) = (z-z')T`. `Re(ab) = Re a Re b - Im a Im b`, so `Re(1-T) = 1 - ⟨Re a Re b⟩ + ⟨Im a Im b⟩ ≥ 1 - (⟨Re a²⟩+⟨Re b²⟩)/2`.
External hypotheses: none (the proof is unconditional; DECISIONS §90 not triggered), so no external limit computation applies. Merged upstream used: `BASelf_exists`/`BAm_self` (`BASelf d L g z (BAm d L g z)` for `0 < z.im`, `MFixedPoint.lean:809`), `BAm_real_eq_of_self` (`:824`), `BAMB_trace_eq_sum`, `BAm_norm_le_one`.

### (ii) One concrete nondegenerate instance
`d = 3`, `L = 4` (`N = 64`), the merged flow point of `(L, g) = (4, 10)` (`CouplingWindow.lean:861-864`: `t0P = BAt0 zS mS`, `EP = BAflowE zS mS`, `m0P = mS/√t0P`, `g0P = √t0P·10`, with `w = 6i/5`, `mS = ⟨(v-w)⁻¹⟩`, `zS = w - mS`, `MFixedPoint.lean:849-868`), `κ = Im mS`. Spectrum of `Ψ^(B)`: `2Σ_j cos(2πk_j/L)` (checked equal to the eigenvalues of the `ℓ¹`-distance-1 adjacency matrix, `Adj`, `Lattice.lean:108`). Premises: `BAReal 3 4 g0P κ EP m0P` (self-consistency, `Im m0P ≥ κ`), `0 < g0P ≤ Λ = 10`, `Im zS > 0`. Tested at 44 values of `η` in `[1e-6, 10]` including `η = κ³/4`, `1`, `3`, `10`; `BAm(E+iη)` by Newton continuation from `η = 2`.
Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2291/inst.py`
```
adjacency eig match: True
mS (-5.134781488891349e-16+0.2619687833792618j) zS (5.134781488891349e-16+0.9380312166207381j) t0 0.2183073194827182 E 1.0989750134607023e-15 g0 4.672336883003174 m0 (-1.0989750134607023e-15+0.5606804259603809j)
Im zS>0: True | g0<=10: True | 0<g0: True | selfS residual 0.0
real-axis self residual (BASelf g0 E m0): 1.1105344375242163e-16 <|a|^2>-1: 0.0
kappa=Im mS= 0.2619687833792618  Im m0= 0.5606804259603809  BAReal (kappa<=Im m0): True  Im m0<=1: True
c=kappa^5/64 = 1.9278255948139518e-05
etas tested: 44  BAbulk: rho_N(E)= 0.17847012257292813 >= kappa/pi= 0.08338725362115895
violations of targets 1,2,3,4,6: {1: np.int64(0), 2: 0, 3: 0, 4: 0, 6: 0}
max target-1 ratio (Im m^2+Im m'^2)|m-m'|/(2 eta): 0.15624737106200529
min over eta<=1 of Im m(E+i eta)/(kappa^5/64): 13285.706028161569
Im m(E+i eta) at eta=kappa^3/4: 0.5584510447933777  >= kappa/2= 0.1309843916896309
Im m(E+i) = 0.2561252412626388  vs eta*kap^2/(eta+3)^2 = 0.004289227716575663
T1 at two complex points: lhs 0.09204326592118678  <= rhs 0.8544003745317532
eta=0.004495: |T|=0.9842<=1, Re(1-T)=1.9842 >= (Im m^2+Im m'^2)/2=0.3131, (m-m')(1-T)-(z-z')T=5.8e-18
   delta=0.0023<=eta+2=2.0045; <|b|^2>=0.9920>=kap^2/(kap+delta)^2=0.9829>=kap^2/(eta+3)^2=0.0076
eta=1: |T|=0.4379<=1, Re(1-T)=1.4379 >= (Im m^2+Im m'^2)/2=0.1900, (m-m')(1-T)-(z-z')T=4.0e-18
   delta=0.6954<=eta+2=3.0000; <|b|^2>=0.2039>=kap^2/(kap+delta)^2=0.0749>=kap^2/(eta+3)^2=0.0043
eta=10: |T|=0.0526<=1, Re(1-T)=1.0526 >= (Im m^2+Im m'^2)/2=0.1590, (m-m')(1-T)-(z-z')T=8.5e-19
   delta=9.4999<=eta+2=12.0000; <|b|^2>=0.0060>=kap^2/(kap+delta)^2=0.0007>=kap^2/(eta+3)^2=0.0004
```
Reading: premises hold (real-axis residual `1.1e-16`, `⟨|a|²⟩ - 1 = 0`, `κ = 0.2620 ≤ Im m0P = 0.5607 ≤ 1`, `0 < g0P = 4.672 ≤ 10`); targets 1, 2, 3, 4 (`c = κ⁵/64 = 1.93e-5`, worst ratio `1.3e4`) and 6 have 0 violations; target 1 ratio max `0.156 ≤ 1`; the identity `(m-m')(1-T) = (z-z')T` holds to `1e-17`. Dispatcher's extra numerics (ticket Preflight (viii), `d = 3`, `L ∈ {4,5,6}`, `g ∈ {0.05, ..., 10}`) were not rerun here (not required by section (a)).

### Verdicts
- Target 1 `BASelf_sub_le` (M1–M2): PASS (derivation re-checked; hypotheses `0 ≤ Im z, Im z'` suffice; no `d, L, g` condition).
- Target 2 `BAm_im_ge_half` (M3): PASS (uses target 1 and `BAm_self` at `E + iη`, `η > 0`).
- Target 3 `BAm_im_ge_mul` (M4): PASS (every `η > 0`; uses `κ ≤ Im m ≤ 1`, `‖m‖,‖m'‖ ≤ 1`).
- Target 4 `BAm_im_lower` (M5): PASS (two branches close, slack in the table).
- Target 5 `baImmLower_holds`: PASS (`c := κ⁵/64`, `NeZero L` from `3 ≤ L`, then target 4; the pin's premises `3 ≤ d`, `0 < Λ`, `0 < g`, `g ≤ Λ` are unused).
- Target 6 `BAm_im_lower_of_bulk` (M6): PASS (`BAbulk_iff_exists` then target 4 at `πκ`; closes 1102 O9 (b) as a lower bound `(πκ)⁵/64`).
Overall verdict: PASS. Check-file compile by the hub: CONTROL `done: Tue Oct  6 11:43:54 UTC 2026 — exit 0, no error lines` (`docs/queue/CONTROL.md:27`).

## (b) Script output — Tue Oct  6 12:01:47 UTC 2026

### Build (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2291`, branch `t/T2291`, commit `58965b6`)
```
$ git log --oneline -1; git status --short
58965b6 T2291: BA-D7 BA/ImmLower, the lower bound on Im m(E + i eta) in the bulk (BAImmLower proved)
$ lake build RBM3D.BA.ImmLower 2>&1 | tail -3   # Tue Oct  6 12:01:47 UTC 2026
info: RBM3D/BA/CouplingWindow.lean:473:48: `exact hb.ne'`
modifies the current goal, which was modified by the flexible tactic `simp` on line 473!
Build completed successfully (3338 jobs).
$ lake build   # whole library, started 11:57:58 UTC (tool log); tail of its output file
Build completed successfully (4097 jobs).
exit=0
$ lake env lean precheck.lean   # import RBM3D; import RBM3D.BA.ImmLower; #assert_rbm_axioms (temporary, uncommitted)
import RBM3D
import RBM3D.BA.ImmLower
#assert_rbm_axioms
exit=0 (recorded 11:59:24 UTC); lines of output:      273; lines mentioning ImmLower: 0
axiom audit: 8360 theorems, 2773 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
```

### Axioms of the 6 public theorems
```
$ lake env lean axioms.lean   # import RBM3D.BA.ImmLower + #print axioms of each
'RBM.BA.BASelf_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAm_im_ge_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAm_im_ge_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAm_im_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baImmLower_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAm_im_lower_of_bulk' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/BA/ImmLower.lean | wc -l
       0
```

### Target statements (extracted by script from `RBM3D/BA/ImmLower.lean`)
```lean
theorem BASelf_sub_le (d L : ℕ) [NeZero L] (g : ℝ) (z z' m m' : ℂ) (hz : 0 ≤ z.im) (hz' : 0 ≤ z'.im)
    (h : BASelf d L g z m) (h' : BASelf d L g z' m') :
    (m.im ^ 2 + m'.im ^ 2) * ‖m - m'‖ ≤ 2 * ‖z - z'‖ := by
theorem BAm_im_ge_half (d L : ℕ) [NeZero L] (g κ E : ℝ) (m : ℂ) (hκ : 0 < κ) (h : BAReal d L g κ E m)
    (η : ℝ) (hη : 0 < η) (hη' : η ≤ κ ^ 3 / 4) :
    κ / 2 ≤ (BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)).im := by
theorem BAm_im_ge_mul (d L : ℕ) [NeZero L] (g κ E : ℝ) (m : ℂ) (hκ : 0 < κ) (h : BAReal d L g κ E m)
    (η : ℝ) (hη : 0 < η) :
    η * κ ^ 2 / (η + 3) ^ 2 ≤ (BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)).im := by
theorem BAm_im_lower (d L : ℕ) [NeZero L] (g κ E : ℝ) (m : ℂ) (hκ : 0 < κ) (h : BAReal d L g κ E m)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    κ ^ 5 / 64 ≤ (BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)).im := by
theorem baImmLower_holds (d : ℕ) (Λ κ : ℝ) : BAImmLower d Λ κ := by
theorem BAm_im_lower_of_bulk (d L : ℕ) [NeZero L] (g κ E : ℝ) (hκ : 0 < κ) (hb : BAbulk d L g κ E)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    (Real.pi * κ) ^ 5 / 64 ≤ (BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)).im := by
```

### Check-file equality (compiled)
`docs/tickets/checks/T2291-check.lean` + `import RBM3D.BA.ImmLower` + 6 lines `example : Y_pin := @RBM.BA.Y` (scratch, not committed):
```
$ lake env lean check_eq.lean > check_eq2.out 2>&1; echo exit=$?
exit=0
lines of output:       65 (the #check lines of the check file); lines starting with error: 0
$ grep -n "^example : .*_pin := @" check_eq.lean
146:example : BASelf_sub_le_pin := @RBM.BA.BASelf_sub_le
147:example : BAm_im_ge_half_pin := @RBM.BA.BAm_im_ge_half
148:example : BAm_im_ge_mul_pin := @RBM.BA.BAm_im_ge_mul
149:example : BAm_im_lower_pin := @RBM.BA.BAm_im_lower
150:example : baImmLower_holds_pin := @RBM.BA.baImmLower_holds
151:example : BAm_im_lower_of_bulk_pin := @RBM.BA.BAm_im_lower_of_bulk
```

### The compiled nonempty instances (namespace `RBM.BA.ImmLowerInst`, section 5 of the file; compiled by the build above)
```lean
namespace RBM.BA.ImmLowerInst

open RBM.BA RBM.BA.MFixedPointInst RBM.BA.CouplingWindowInst

/-- (I1) The pin `BAImmLower` itself, at `d = 3` and arbitrary `Λ`, `κ`. -/
example (Λ κ : ℝ) : BAImmLower 3 Λ κ := baImmLower_holds 3 Λ κ

/-- (I2) The pin's conclusion at the merged flow point: `c = (Im m_S)⁵/64`, `η ∈ (0, 1]`. -/
example : ∀ η : ℝ, 0 < η → η ≤ 1 →
    (mS 4 10).im ^ 5 / 64 ≤ (BAm 3 4 g0P ((EP : ℂ) + (η : ℂ) * Complex.I)).im :=
  fun η hη hη1 => BAm_im_lower 3 4 g0P (mS 4 10).im EP m0P (selfS 4 10).1 flowP_real η hη hη1

/-- (I3) Target 1 between the real point `(EP, m0P)` and `(EP + iη, m(EP + iη))`. -/
example : ∀ η : ℝ, 0 < η →
    (m0P.im ^ 2 + (BAm 3 4 g0P ((EP : ℂ) + (η : ℂ) * Complex.I)).im ^ 2) *
        ‖m0P - BAm 3 4 g0P ((EP : ℂ) + (η : ℂ) * Complex.I)‖
      ≤ 2 * ‖(EP : ℂ) - ((EP : ℂ) + (η : ℂ) * Complex.I)‖ := by
  intro η hη
  have hz' : 0 < ((EP : ℂ) + (η : ℂ) * Complex.I).im := by simp [hη]
  exact BASelf_sub_le 3 4 g0P (EP : ℂ) ((EP : ℂ) + (η : ℂ) * Complex.I) m0P _ (by simp) hz'.le
    flowP_data.2.2 (BAm_self 3 4 g0P _ hz')

/-- (I4) Target 6 at the `ρ`-bulk datum of the flow point: `ρ_4(EP) ≥ (Im m_S)/π`, `c = ((Im m_S))⁵/64`. -/
example : ∀ η : ℝ, 0 < η → η ≤ 1 →
    (Real.pi * ((mS 4 10).im / Real.pi)) ^ 5 / 64 ≤
      (BAm 3 4 g0P ((EP : ℂ) + (η : ℂ) * Complex.I)).im := by
  intro η hη hη1
  have hκ : 0 < (mS 4 10).im / Real.pi := div_pos (selfS 4 10).1 Real.pi_pos
  have hb : BAbulk 3 4 g0P ((mS 4 10).im / Real.pi) EP := by
    unfold BAbulk BArho
    rw [BAm_real_eq_of_self 3 4 g0P EP m0P flowP_real.1]
    exact div_le_div_of_nonneg_right flowP_real.2 Real.pi_pos.le
  exact BAm_im_lower_of_bulk 3 4 g0P _ EP hκ hb η hη hη1

/-- Target 2 at the flow point, `η = κ³/4` (the end of its range), `κ = Im m_S`. -/
example : (mS 4 10).im / 2 ≤
    (BAm 3 4 g0P ((EP : ℂ) + (((mS 4 10).im ^ 3 / 4 : ℝ) : ℂ) * Complex.I)).im :=
  BAm_im_ge_half 3 4 g0P (mS 4 10).im EP m0P (selfS 4 10).1 flowP_real ((mS 4 10).im ^ 3 / 4)
    (div_pos (pow_pos (selfS 4 10).1 3) (by norm_num)) le_rfl

/-- Target 3 at the flow point, `η = 1`. -/
example : (1 : ℝ) * (mS 4 10).im ^ 2 / (1 + 3) ^ 2 ≤
    (BAm 3 4 g0P ((EP : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)).im :=
  BAm_im_ge_mul 3 4 g0P (mS 4 10).im EP m0P (selfS 4 10).1 flowP_real 1 one_pos

end RBM.BA.ImmLowerInst
```

### Name-clash grep, diff-stat, imports, private helpers
```
$ bash clash.sh   # grep -rnw over RBM3D/ (Probe excluded) and docs/tickets/*.md
BASelf_sub_le: RBM3D (outside ImmLower.lean, Probe excluded): 0 hits; tickets naming it: T2291.md 
BAm_im_ge_half: RBM3D (outside ImmLower.lean, Probe excluded): 0 hits; tickets naming it: T2291.md 
BAm_im_ge_mul: RBM3D (outside ImmLower.lean, Probe excluded): 0 hits; tickets naming it: T2291.md 
BAm_im_lower: RBM3D (outside ImmLower.lean, Probe excluded): 0 hits; tickets naming it: T2291.md 
baImmLower_holds: RBM3D (outside ImmLower.lean, Probe excluded): 0 hits; tickets naming it: T2291.md 
BAm_im_lower_of_bulk: RBM3D (outside ImmLower.lean, Probe excluded): 0 hits; tickets naming it: T2291.md 
ImmLowerInst: RBM3D (outside ImmLower.lean, Probe excluded): 0 hits; tickets naming it: T2291.md 
ImmLower_ (prefix): RBM3D outside ImmLower.lean: 0 hits; tickets: T2291.md 
$ git diff --stat main...t/T2291
 RBM3D/BA/ImmLower.lean | 479 +++++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 479 insertions(+)
$ grep -n "^import" RBM3D/BA/ImmLower.lean
7:import RBM3D.BA.Ward
8:import RBM3D.BA.CouplingWindow
9:import Mathlib.Algebra.Order.Chebyshev
10:import Mathlib.Analysis.Complex.Norm
$ grep -n "private\|^theorem\|^def\|^example" RBM3D/BA/ImmLower.lean | cut -c1-110
57:private theorem ImmLower_inv_im (v : ℝ) (w : ℂ) (hw : 0 < w.im) :
63:private theorem ImmLower_inv_ne (v : ℝ) (w : ℂ) (hw : 0 < w.im) : ((v : ℂ) - w) ≠ 0 := by
70:private theorem ImmLower_norm_ge (v : ℝ) (w : ℂ) (hw : 0 < w.im) : w.im ≤ ‖(v : ℂ) - w‖ := by
76:private theorem ImmLower_inv_norm_le (v : ℝ) (w : ℂ) (hw : 0 < w.im) : ‖((v : ℂ) - w)⁻¹‖ ≤ w.im⁻¹
81:private theorem ImmLower_re_sq_avg (N : ℝ) (hN : (Fintype.card ι : ℝ) = N) (hNpos : 0 < N) (a : ι
103:private theorem ImmLower_two_point (N : ℝ) (hN : (Fintype.card ι : ℝ) = N) (hNpos : 0 < N) (a b 
139:private theorem ImmLower_b_ge (w w' : ℂ) (κ δ : ℝ) (hκ : 0 < κ) (hδ : 0 ≤ δ) (hw : κ ≤ ‖w‖) (hw'
165:private def ImmLower_a (d L : ℕ) [NeZero L] (g : ℝ) (z m : ℂ) (i : Zd d L) : ℂ :=
168:private theorem ImmLower_zm_pos {g : ℝ} {z m : ℂ} (hz : 0 ≤ z.im) (h : BASelf d L g z m) : 0 < (
171:private theorem ImmLower_N_pos (d L : ℕ) [NeZero L] : 0 < ((L ^ d : ℕ) : ℝ) := by
175:private theorem ImmLower_card (d L : ℕ) [NeZero L] : (Fintype.card (Zd d L) : ℝ) = ((L ^ d : ℕ) 
179:private theorem ImmLower_sum {g : ℝ} {z m : ℂ} (hz : 0 ≤ z.im) (h : BASelf d L g z m) :
190:private theorem ImmLower_a_im {g : ℝ} {z m : ℂ} (hz : 0 ≤ z.im) (h : BASelf d L g z m) (i : Zd d
194:private theorem ImmLower_a_ne {g : ℝ} {z m : ℂ} (hz : 0 ≤ z.im) (h : BASelf d L g z m) (i : Zd d
198:private theorem ImmLower_a_im_pos {g : ℝ} {z m : ℂ} (hz : 0 ≤ z.im) (h : BASelf d L g z m) (i : 
204:private theorem ImmLower_im_avg {g : ℝ} {z m : ℂ} (hz : 0 ≤ z.im) (h : BASelf d L g z m) :
211:private theorem ImmLower_ward {g : ℝ} {z m : ℂ} (hz : 0 ≤ z.im) (h : BASelf d L g z m) :
224:private theorem ImmLower_A_le {g : ℝ} {z m : ℂ} (hz : 0 ≤ z.im) (h : BASelf d L g z m) :
234:private theorem ImmLower_A_eq_real {g : ℝ} {z m : ℂ} (hz : z.im = 0) (h : BASelf d L g z m) :
252:theorem BASelf_sub_le (d L : ℕ) [NeZero L] (g : ℝ) (z z' m m' : ℂ) (hz : 0 ≤ z.im) (hz' : 0 ≤ z'
298:private theorem ImmLower_norm_eta (η : ℝ) (hη : 0 < η) : ‖(η : ℂ) * Complex.I‖ = η := by
302:theorem BAm_im_ge_half (d L : ℕ) [NeZero L] (g κ E : ℝ) (m : ℂ) (hκ : 0 < κ) (h : BAReal d L g κ
327:theorem BAm_im_ge_mul (d L : ℕ) [NeZero L] (g κ E : ℝ) (m : ℂ) (hκ : 0 < κ) (h : BAReal d L g κ 
391:theorem BAm_im_lower (d L : ℕ) [NeZero L] (g κ E : ℝ) (m : ℂ) (hκ : 0 < κ) (h : BAReal d L g κ E
414:theorem baImmLower_holds (d : ℕ) (Λ κ : ℝ) : BAImmLower d Λ κ := by
424:theorem BAm_im_lower_of_bulk (d L : ℕ) [NeZero L] (g κ E : ℝ) (hκ : 0 < κ) (hb : BAbulk d L g κ 
439:example (Λ κ : ℝ) : BAImmLower 3 Λ κ := baImmLower_holds 3 Λ κ
442:example : ∀ η : ℝ, 0 < η → η ≤ 1 →
447:example : ∀ η : ℝ, 0 < η →
457:example : ∀ η : ℝ, 0 < η → η ≤ 1 →
469:example : (mS 4 10).im / 2 ≤
475:example : (1 : ℝ) * (mS 4 10).im ^ 2 / (1 + 3) ^ 2 ≤
```

### Narrative (b)
- Route as in the ticket (M0-M5), no deviation, no `(a′)` correction needed (section (a) was not edited). File `RBM3D/BA/ImmLower.lean`, 479 lines (ticket estimate 400/650/1000; no cut, no `T2291a`).
- Layout: section 1 generic lemmas over a `Fintype ι` (private `ImmLower_*`: `Im (v-w)⁻¹ = Im w |(v-w)⁻¹|²`, Jensen `⟨Re a²⟩ ≤ 1 - Im m²`, the two-point bounds `‖T‖ ≤ 1` and `Re(1-T) ≥ (Im m²+Im m'²)/2`, the pointwise `|b_i| ≥ |a_i| κ/(κ+δ)`); section 2 the spectral form over `Zd d L` (`BAMB_trace_eq_sum`; averaged Ward `(Im z + Im m)⟨|a|²⟩ = Im m`); section 3 target 1; section 4 targets 2-6; section 5 the instances.
- Constants: the pin's `c = κ⁵/64` (depends on `κ` only, chosen before `L, g, E, m`); target 6 gives `(πκ)⁵/64`; target 1 has constant 2 (the merged real-axis `BAgapReal` has 1 at `z = z'`).
- Unused premises of the pin `BAImmLower` (kept in the pin, absent from theorems 1-4, 6): `3 ≤ d`, `0 < Λ`, `0 < g`, `g ≤ Λ`; `3 ≤ L` is used only through `NeZero L` (`baImmLower_holds`). Theorems 1-4 and 6 carry `[NeZero L]` and no `d`, `Λ`, `g` hypothesis.
- Imports exactly the four of the ticket. `BAm_norm_le_one` (`Ward.lean`) gives `Im m ≤ 1`; `RBM3D.BA.CouplingWindow` is imported only for the instance data (`CouplingWindowInst`); no import of `BA.Boundary`; no merged file changed.
- Instances: (I1)-(I4) as in the ticket, plus targets 2 and 3 at the flow point. Target 2 is applied at `η = κ³/4` with `κ = Im m_S` (the end of its range, `le_rfl`); target 3 at `η = 1`. Every hypothesis is discharged by `flowP_real`, `flowP_data`, `selfS`, `BAm_self`; none is left open.
- Registry pre-check (`import RBM3D` + `import RBM3D.BA.ImmLower` + `#assert_rbm_axioms`): exit 0; no output line mentions `ImmLower`, so no name is flagged and `RBM3D/Test/Axioms.lean` is untouched; `git diff --stat main...t/T2291` lists only `RBM3D/BA/ImmLower.lean`.
- 1102 O9 (b) (DECISIONS §95 (4)): target 6 `BAm_im_lower_of_bulk` states `ρ_N(E) ≥ κ` (`BAbulk`) gives `(πκ)⁵/64 ≤ Im m(E + iη)`, `η ∈ (0, 1]`; the lossless `BAProp8` (O9 (a)) is not touched.
- Preflight (viii) numerics (`L ∈ {4,5,6}`, five `g`) were run by the dispatcher, not rerun here; the Lean statements are unconditional and compiled.
- Ports: none from RBM1D/RBM2D (no file read or copied from them), so no RBM1D/RBM2D diff-stat applies.

## (c) Verified Mathlib names (`lake env lean names.lean`, `#check` of each, exit 0, 0 error lines; root namespace unless `Complex.`)
- `sq_sum_le_card_mul_sum_sq`, `Complex.abs_im_le_norm`, `Complex.im_le_norm`, `Complex.re_le_norm`, `Complex.inv_im` (`(z⁻¹).im = -z.im / normSq z`), `Complex.normSq_inv`, `Complex.sq_norm`, `Complex.normSq_apply`
- `Complex.re_ofReal_mul`, `Complex.im_ofReal_mul`, `Complex.re_sum`, `Complex.im_sum`, `Complex.norm_real`, `Complex.norm_I`
- `sub_add_cancel_left`, `inv_anti₀`, `div_le_div_iff₀`, `div_le_div_of_nonneg_left`, `div_le_div_of_nonneg_right`, `pow_le_pow_left₀`, `pow_le_one₀`, `le_div_iff₀`, `norm_sum_le`, `le_of_mul_le_mul_left`, `mul_lt_mul_of_pos_left`
- Names not used (listed in the ticket, not needed): `BAself_im_le_one`, `BAm_im_nonneg` (not imported by any proof; `CouplingWindow` serves the instances only).
- Names verified absent: none searched (no invented names; every name above compiled).

## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none new. The difference "`ρ_N(E) ≥ κ` bulk vs the paper's `|E| ≤ e_λ − κ` / `lem:propM` (2) `Im m ≳ 1` (`7_8:1908`)" is the existing delta D403 (`docs/paper-deltas.md:1362`, found by `grep -n "§51" docs/paper-deltas.md`). No `T2291a`.
- Open issues: none. No hypothesis was added, no target weakened, no signature changed (the pin `BAImmLower` is proved verbatim; check-file equality compiled above).
- For the dispatcher: the plan row BA-D7 can now read "depends on BA-D2 and BA-D3 (Ward)" (`BAm_norm_le_one`), as the ticket says; the file imports `RBM3D.BA.Ward` and `RBM3D.BA.CouplingWindow` (instances only), not `BA.Boundary`.
- Hub at merge: add `import RBM3D.BA.ImmLower` after the last `import` line of `RBM3D.lean`; the full `lake build` and the registry pre-check above already passed on this branch without that import (library target `RBM3D`, 4097 jobs).
