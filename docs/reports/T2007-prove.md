Prover model: claude-sonnet-5-5

## (a) Math preflight — Fri Oct  2 23:54:03 UTC 2026

Target 2 (`Prop5Short d Λ κ`, pinned text): `Θ = Ring.inverse (1 − ξ•SB)`, `ξ = t·μ`, `μ = m(σ)²`, `‖m‖=1`, `κ ≤ Im m`.
Write `m = e^{iφ}`, `u = sin²φ = (Im m)² ≥ κ²`; `σ = false` replaces `μ` by `μ̄`, and `|1 − xμ̄| = |1 − xμ|`, so one case covers both.
Targets 1 (pins, bridges, refutations) are copies of the compiled probe/check text; they add no exponent. Only target 2 carries mathematics.

### (i) Exponent table  (`s := (1+2dλ²)⁻¹`, `x := t s ∈ [0,1)`, `λ = g ∈ (0,Λ]`, `κ' := min(κ,1)`; for `κ > 1` the hypothesis `κ ≤ Im m` is vacuous)

| Quantity | Value / formula | Constraint | Bound / slack |
|---|---|---|---|
| `s = SB 0 0` | `(1+2dλ²)⁻¹` | `SB = s·1 + λ²s·Adj` (L ≥ 3: `#{zdistD = 1} = 2d`, checked below) | `s_min := (1+2dΛ²)⁻¹ ≤ s ≤ 1`; d=3, Λ=1: `s_min = 1/7` |
| `1 − s` | `2dλ² s` | row sum of `λ²s·Adj` is `2dλ²s = 1−s` (so `‖λ²s·Adj‖_{∞→∞} = 1−s`) | `1 − s ≤ 2dλ²`; this is the one factor `λ²` per `k ≥ 1` term |
| Gap `A = |1 − tμs|` | `A² = (1−x)² + 4x·u` (from `|1−xe^{2iφ}|² = (1−x)² + 2x(1−cos 2φ)`) | need `A ≥ c(κ) > 0` for all `t∈[0,1)`, `λ`, `L` | `A² ≥ κ'²(1−x)² + 4xκ'² = κ'²(1+x)² ≥ κ'²`, so **`A ≥ κ'`**; no degeneration as `t→1` since `μ ≠ 1` (`Im m ≥ κ`). For `m = i` (`u = 1`): `A = 1+x ≥ 1` |
| `ρ = t(1−s)/A` | Neumann ratio for `N = tμλ²s·Adj`, `‖N/(1−tμs)‖_{∞→∞} ≤ ρ` | need `ρ ≤ ρ₀ < 1` with `ρ₀` depending on `(d,Λ,κ)` only | `ρ⁻² = ((1/t−s)² + 4su/t)/(1−s)²` (from `A² = (1−ts)²+4tsu`) is decreasing in `t` (as `1/t − s ≥ 1−s > 0`), so the sup is at `t = 1` and `ρ² ≤ (1−s)²/((1−s)²+4su) = 1/(1+4su/(1−s)²) ≤ 1/(1+4 s_min κ'²)`. So **`ρ₀ = (1 + 4κ'² s_min)^{-1/2}`**; d=3,Λ=1,κ=1/2: `ρ₀ = 0.935414`, `1−ρ₀ = 0.064586` |
| Ticket's `ρ ≤ 1 − s sin²φ/2` | claim in the ticket | implied by the above | holds with slack: grid `max ρ/(1−s u/2) = 0.9316` (script below); `ρ₀ ≤ 1 − s_min κ²/2 = 0.98214` also holds |
| Decay rate `c` | `c = −log ρ₀` | `c > 0` | `0.066766` (d=3,Λ=1,κ=1/2) |
| Support | `Adj^k(0,a) = 0` for `k < zdistD a` | torus ℓ¹ distance | gives `k ≥ |a|` in the sum |
| `Σ_{k}` term | `|Θ-term_k| = |A'|^{-(k+1)} (t(1−s))^k (Adj/2d)^k(0,a) ≤ A⁻¹ρ^k` (`A' = 1 − tμs`, `(Adj/2d)^k` stochastic) | | `k ≥ 1`: `ρ^k ≤ ρ^{k−1}·2dλ²s/A`, one `λ²` extracted |
| `a = 0` | `|Θ(0,0)| ≤ A⁻¹ Σ_k ρ^k` | | `C₀ = 1/(κ'(1−ρ₀))`; d=3: `30.967` |
| `a ≠ 0` | `|Θ(0,a)| ≤ (2dλ²/κ'²)·Σ_{k≥|a|} ρ₀^{k−1} = (2dλ²/(κ'²(1−ρ₀)))ρ₀^{|a|−1}` | | `C₁ = 2d/(κ'²ρ₀(1−ρ₀))`, rate `c`; d=3: `397.257` |
| Output constants | `C = max(C₀,C₁) = C₁` (as `κ' ≤ 1`, `d ≥ 1`), `c = −log ρ₀` | depend on `(d,Λ,κ)` only, **not** on `L`, `g`, `t`, `m` | `C = 397.257` at (3,1,1/2) |

Regimes. `λ → 0`: `s → 1`, `1−s → 0`, `ρ → 0`; `Θ(0,0) → (1−tμ)⁻¹` with `|1−tμ| ≥ κ'` (gap bound at `s = 1`); off-diagonal `≲ λ²` (one `Adj` factor). `λ = Λ`: `s = s_min`, the worst case of the bound `1/(1+4sκ'²)`, covered by `ρ₀`. `t → 1`: `A ≥ κ'` and `ρ ≤ ρ₀` are uniform in `t ∈ [0,1)` (the `t`-monotonicity of `ρ` gives the sup at `t = 1`); the Neumann series is convergent for each `t < 1` and the constant is `t`-free. No `ℓ_t`, `B_{t,K}` or `(1−t)⁻¹` appears in the pin, so no loss at `t → 1` is to be absorbed.
Convention check against the pin: `Prop5Short` bounds by `C·(1_{a=0} + g²e^{-c·zdistD a})`; the proof gives exactly this with the `C, c` above for `a = 0` (term `1`, and `g²e^0 ≥ 0` helps) and `a ≠ 0` (term `g²e^{-c|a|}` via `ρ₀^{|a|−1} = ρ₀⁻¹ e^{-c|a|}`).
Hypotheses of the pin are not needed beyond: `L ≥ 3` (torus nearest-neighbour count `2d`; for `L ≥ 3` the `±e_i` are distinct), `d ≥ 1` (`d ≥ 3` is not used), `Λ > 0`, `κ > 0`.

### (ii) Concrete instance: `d = 3`, `Λ = 1`, `κ = 1/2`; `L ∈ {5, 9, 17}` (and `L = 3`), `g ∈ {1, 0.01}`, `t ∈ {0, 0.9, 0.999}`, `m ∈ {i, e^{iπ/3}}`, both `σ` (`Im m ≥ 1/2` holds: `1` and `√3/2`), all `a`
Script `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/pf.py` (python, no Lean) (exact `Θ(0,a) = ifftn(1/(1 − ξ ŝ(k)))`, `ŝ(k) = s(1 + 2λ²Σ_i cos(2πk_i/L))`, `|a| = Σ_i min(a_i, L−a_i)`), run `python3 pf.py`:
```
s_min=0.142857 rho0=0.935414 c=0.066766 1-rho0=0.064586 C0=30.967 C1=397.257 C=397.257
check rho0<=1-s_min*kap^2/2: True 0.9821428571428571
min A/kappa over grid = 1.7321 (>=1 needed); max rho/rho0 = 0.9782 (<=1 needed)
L=5  max |Theta(0,a)|/bound = 0.0025 (<=1 needed)
L=9  max |Theta(0,a)|/bound = 0.0025 (<=1 needed)
L=17  max |Theta(0,a)|/bound = 0.0025 (<=1 needed)
max rho/(1-s sin^2phi/2) = 0.9316 (<=1 needed)
L=3 #{a: zdistD a =1} = 6 (2d=6)
L=5 #{a: zdistD a =1} = 6 (2d=6)
L=3 ratio 0.0012069221151374296
```
(`bound = C·(1_{a=0} + g²e^{-c|a|})` with the constants above; the `A/κ` / `ρ/ρ₀` grid is over 60 values `λ ∈ [10⁻³,1]`, 200 values of `t ∈ [0,1)` plus `0.999, 0.999999`, 200 values of `φ ∈ [arcsin κ, π−arcsin κ]`, both signs of `σ`.)
The pin therefore holds with these constants at the instance, with large slack (ratio `≤ 0.0025`, since `C` is crude); the Lean instance in the ticket (`L = 5`, `g = 1/2`, `t = 9/10`, `m = i`, `σ = true`, `a = 0` and `a ≠ 0`) lies inside this set (`g = 1/2 ∈ (0,Λ]`, `κ = 1/2 ≤ Im i = 1`).
No external hypothesis is involved in target 2 (it uses only merged declarations); the pins of target 1 are `Prop` definitions (no hypothesis).

### Verdicts
- Target 1 (`Propagator/Pins.lean`): PASS. Pure copy of compiled probe/check text and probe proofs; no exponent.
- Target 2 (`prop5Short_holds`): PASS. Constants `C = max(C₀,C₁)`, `c = −log ρ₀`, `ρ₀ = (1+4κ'²/(1+2dΛ²))^{-1/2}`, `κ' = min(κ,1)`, independent of `L, g, t, m, σ, a`; the gap `A ≥ κ'` holds for all `t ∈ [0,1)`. The ticket's `ρ ≤ 1 − s sin²φ/2` is true (used only as a cross-check).

## (b) Script output — Sat Oct  3 00:11:05 UTC 2026 (branch `t/T2007` at 29230e9, parent a150c32, base main 6a555f7)
Scripts: `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2007_{all.sh,pindiff.py,port.py,const.py,clash.sh,axioms.lean,names.lean}`; the block below is `bash T2007_all.sh` verbatim, run from the worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2007`.
```
$ date -u; git log --oneline -2; git status --short | wc -l
Sat Oct  3 00:11:05 UTC 2026
29230e9 T2007: reword the instances docstring in Pins.lean
a150c32 T2007: pins of lem_propTH properties 5-8, bridges, refutations, and prop5Short_holds
       0
$ lake build RBM3D.Propagator.Pins RBM3D.Propagator.Prop5Short 2>&1 | grep -v "^trace" | tail -3
Build completed successfully (2435 jobs).
$ lake env lean T2007_axioms.lean | awk (19 public declarations of the two files; no other message line except the #check)
RBM.prop5Short_holds : ∀ (d : ℕ) (Λ κ : ℝ), RBM.Prop5Short d Λ κ
axiom lines: 19  exactly [propext, Classical.choice, Quot.sound]: 19
names: PropSpin Prop5Decay Prop5Short Prop6Diff1 Prop7Diff2 Prop8ZeroMode Prop5to8 PropThetaQ PropThetaQ_Theta_eq Prop5DecayQ Prop5Decay.toQ Prop5Short.thetaDecayShort Prop5Decay.thetaDecay Prop8ZeroMode.thetaZeroMode Prop6Old_false Prop7Old_false PropTH_false Prop5_needs_Lambda prop5Short_holds
$ python3 T2007_pindiff.py <check file> RBM3D/Propagator/Pins.lean | awk (summary)   # whole blocks incl. docstrings; RBM.T2007Check -> RBM
9/9 pin blocks identical: PropSpin Prop5Decay Prop5Short Prop6Diff1 Prop7Diff2 Prop8ZeroMode Prop5to8 PropThetaQ Prop5DecayQ
$ git show d6e6054:RBM3D/Probe/T2003Pins.lean > T2007_probe.lean; python3 T2007_pindiff.py T2007_probe.lean RBM3D/Propagator/Pins.lean | awk (summary)
9/9 pin blocks identical
$ awk (theorem signatures, text up to ":= by" or ":=") RBM3D/Propagator/Prop5Short.lean RBM3D/Propagator/Pins.lean
Prop5Short.lean:400: theorem prop5Short_holds (d : ℕ) (Λ κ : ℝ) : Prop5Short d Λ κ := by
Pins.lean:157: theorem Prop6Old_false (d : ℕ) (hd : 3 ≤ d) (g : ℝ) (hg : 0 < g) (m : ℂ) (hm : ‖m‖ = 1) :
Pins.lean:158:     ¬ ThetaDiffOne d g m := by
Pins.lean:202: theorem Prop7Old_false (d : ℕ) (hd : 3 ≤ d) (g : ℝ) (hg : 0 < g) (m : ℂ) (hm : ‖m‖ = 1) :
Pins.lean:203:     ¬ ThetaDiffTwo d g m := by
Pins.lean:250: theorem PropTH_false (d : ℕ) (hd : 3 ≤ d) (g : ℝ) (hg : 0 < g) (m : ℂ) (hm : ‖m‖ = 1) :
Pins.lean:251:     ¬ PropTH d g m :=
Pins.lean:261: theorem Prop5_needs_Lambda (d : ℕ) (hd : 1 ≤ d) :
Pins.lean:262:     ¬ ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
Pins.lean:263:       ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g →
Pins.lean:264:         ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 1 → ∀ σ₁ σ₂ : Bool, ∀ a : Zd d L,
Pins.lean:265:           haveI : NeZero L := ⟨by omega⟩
Pins.lean:266:           ‖Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 a‖
Pins.lean:267:             ≤ C * Bparam d L g t (zdistD d L a)
Pins.lean:268:                 * Real.exp (-c * (zdistD d L a : ℝ) / ellT L g t) := by
Pins.lean:316: theorem Prop5Short.thetaDecayShort {d : ℕ} {g : ℝ} {m : ℂ} (h : Prop5Short d g m.im) :
Pins.lean:317:     ThetaDecayShort d g m := by
Pins.lean:325: theorem Prop5Decay.thetaDecay {d : ℕ} {g : ℝ} (h : Prop5Decay d g) (m : ℂ) : ThetaDecay d g m := by
Pins.lean:334: theorem Prop8ZeroMode.thetaZeroMode {d : ℕ} {Λ κ g : ℝ} (h : Prop8ZeroMode d Λ κ) (hg : 0 < g)
Pins.lean:335:     (hgΛ : g ≤ Λ) (hκ : 0 < κ) {m : ℂ} (hm : ‖m‖ = 1) (hmi : κ ≤ m.im) (σ₁ σ₂ : Bool) :
Pins.lean:336:     ThetaZeroMode d g (PropSpin m σ₁ * PropSpin m σ₂) := by
Pins.lean:364: theorem PropThetaQ_Theta_eq (d L : ℕ) [NeZero L] (g : ℝ) (t : ℝ) (μ : ℂ) :
Pins.lean:365:     Theta d L g ((t : ℂ) * μ) = PropThetaQ ((μ : ℂ) • SB d L g) t := by
Pins.lean:380: theorem Prop5Decay.toQ {d : ℕ} {Λ : ℝ} (h : Prop5Decay d Λ) (hd : 3 ≤ d) (hΛ : 0 < Λ) (m : ℂ)
Pins.lean:381:     (hm : ‖m‖ = 1) :
Pins.lean:382:     Prop5DecayQ d Λ (fun L [NeZero L] g σ₁ σ₂ => (PropSpin m σ₁ * PropSpin m σ₂) • SB d L g) := by
$ sed -n "/Compiled nonempty instances/,\$p" RBM3D/Propagator/Prop5Short.lean   # the instance of the target (compiled by the build above)
/-! ### Compiled nonempty instances

`prop5Short_holds 3 1 (1/2)` applied at `L = 5`, `g = 1/2`, `t = 9/10`, `m = I` (`‖I‖ = 1`,
`1/2 ≤ Im I = 1`), `σ = true` (`ξ = t m²`), at `a = 0` and at `a = (1,0,0) ≠ 0`, `|a| = 1`;
every hypothesis is discharged. -/

example : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
    ‖Theta 3 5 (1 / 2) (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I true))
        0 0‖
      ≤ C * ((if (0 : Zd 3 5) = 0 then (1 : ℝ) else 0)
        + (1 / 2 : ℝ) ^ 2 * Real.exp (-c * (zdistD 3 5 (0 : Zd 3 5) : ℝ))) := by
  obtain ⟨C, hC, c, hc, H⟩ := prop5Short_holds 3 1 (1 / 2) (by norm_num) (by norm_num)
    (by norm_num)
  exact ⟨C, hC, c, hc, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (9 / 10)
    (by norm_num) (by norm_num) Complex.I Complex.norm_I (by norm_num) true 0⟩

example : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ (![1, 0, 0] : Zd 3 5) ≠ 0
    ∧ zdistD 3 5 (![1, 0, 0] : Zd 3 5) = 1 ∧
    ‖Theta 3 5 (1 / 2) (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I true))
        0 ![1, 0, 0]‖
      ≤ C * ((if (![1, 0, 0] : Zd 3 5) = 0 then (1 : ℝ) else 0)
        + (1 / 2 : ℝ) ^ 2 * Real.exp (-c * (zdistD 3 5 (![1, 0, 0] : Zd 3 5) : ℝ))) := by
  obtain ⟨C, hC, c, hc, H⟩ := prop5Short_holds 3 1 (1 / 2) (by norm_num) (by norm_num)
    (by norm_num)
  exact ⟨C, hC, c, hc, by decide, by decide, H 5 (by norm_num) (1 / 2) (by norm_num)
    (by norm_num) (9 / 10) (by norm_num) (by norm_num) Complex.I Complex.norm_I (by norm_num)
    true ![1, 0, 0]⟩

/-- The pin proves the merged consumer interface `ThetaDecayShort` for every `d`, `g`, `m`
(`Loop/*` and `Kernel/*` assume it). -/
example : ∀ (d : ℕ) (g : ℝ) (m : ℂ), ThetaDecayShort d g m :=
  fun d g m => (prop5Short_holds d g m.im).thetaDecayShort

example : ThetaDecayShort 3 (1 / 2) Complex.I :=
  (prop5Short_holds 3 (1 / 2) Complex.I.im).thetaDecayShort

/-- With `Prop5Decay` and `Prop8ZeroMode` still hypotheses, the bundle `Prop5to8` has its
`short` field proved. -/
example (h5 : Prop5Decay 3 1) (h6 : Prop6Diff1 3 1 (1 / 2) (1 / 2))
    (h7 : Prop7Diff2 3 1 (1 / 2) (1 / 2)) (h8 : Prop8ZeroMode 3 1 (1 / 2)) :
    Prop5to8 3 1 (1 / 2) (1 / 2) :=
  ⟨h5, prop5Short_holds 3 1 (1 / 2), h6, h7, h8⟩

end RBM
$ grep -n "^example" RBM3D/Propagator/Pins.lean   # instances of the Pins.lean theorems (pins of other gates stay hypotheses)
394:example : PropSpin Complex.I true = Complex.I ∧ PropSpin Complex.I false = -Complex.I := by
397:example : Theta 3 5 (1 / 2) (((9 / 10 : ℝ) : ℂ) * Complex.I)
401:example (h : Prop5Decay 3 1) : ThetaDecay 3 1 Complex.I := h.thetaDecay Complex.I
403:example (h : Prop5Decay 3 1) :
408:example (h : Prop5Short 3 (1 / 2) Complex.I.im) : ThetaDecayShort 3 (1 / 2) Complex.I :=
411:example (h : Prop8ZeroMode 3 1 (1 / 2)) :
416:example (h5 : Prop5Decay 3 1) (h5s : Prop5Short 3 1 (1 / 2)) (h6 : Prop6Diff1 3 1 (1 / 2) (1 / 2))
421:example : ¬ ThetaDiffOne 3 (1 / 2) Complex.I :=
424:example : ¬ ThetaDiffTwo 3 (1 / 2) Complex.I :=
427:example : ¬ PropTH 3 (1 / 2) Complex.I :=
430:example : ¬ ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
$ python3 T2007_const.py   # Lean constants at (d,Lambda,kappa)=(3,1,1/2); exact Theta(0,a) by Fourier sum
kappa'=0.5 smin=0.142857 q=0.875000 r=0.937500 r2=0.968750 theta=0.967742 c=0.032790 C=883.200
max |Theta(0,a)|/bound over L in {5,9}, g in {1,.5,.01}, t in {0,.9,.999}, m in {i,e^{i pi/3}}, both sigma, all a: 0.00113
instance L=5 g=1/2 t=9/10 m=i sigma=true a= (0, 0, 0)  |Theta(0,a)| = 0.756004  bound = 1104.0
instance L=5 g=1/2 t=9/10 m=i sigma=true a= (1, 0, 0)  |Theta(0,a)| = 0.052158  bound = 213.677
$ python3 T2007_port.py   # probe d6e6054 -> Pins.lean: probe text contained verbatim after probe_->pins_ rename
PropThetaQ_Theta_eq            probe lines 480-482  verbatim in Pins.lean (probe_->pins_): True
Prop5Decay.toQ                 probe lines 495-501  verbatim in Pins.lean (probe_->pins_): True
Prop5Short.thetaDecayShort     probe lines 434-440  verbatim in Pins.lean (probe_->pins_): True
Prop5Decay.thetaDecay          probe lines 442-448  verbatim in Pins.lean (probe_->pins_): True
Prop8ZeroMode.thetaZeroMode    probe lines 450-464  verbatim in Pins.lean (probe_->pins_): True
Prop6Old_false                 probe lines 277-317  verbatim in Pins.lean (probe_->pins_): True
Prop7Old_false                 probe lines 320-364  verbatim in Pins.lean (probe_->pins_): True
PropTH_false                   probe lines 367-369  verbatim in Pins.lean (probe_->pins_): True
Prop5_needs_Lambda             probe lines 377-410  verbatim in Pins.lean (probe_->pins_): True
probe_Theta_zero               probe lines 241-242  verbatim in Pins.lean (probe_->pins_): True
probeAxis                      probe lines 244-245  verbatim in Pins.lean (probe_->pins_): True
probe_zdist_axis               probe lines 247-251  verbatim in Pins.lean (probe_->pins_): True
probe_zdistD_axis              probe lines 253-260  verbatim in Pins.lean (probe_->pins_): True
probe_arith                    probe lines 263-275  verbatim in Pins.lean (probe_->pins_): True
probe_exists_sq                probe lines 424-432  verbatim in Pins.lean (probe_->pins_): True
$ bash T2007_clash.sh | awk (summary)   # grep -rnw --include=*.lean <name> RBM3D RBM3D.lean, minus the two new files
19 new public names checked; total occurrences outside the two new files: 0
$ grep -cE 'sorry|admit|native_decide|^ *axiom ' RBM3D/Propagator/Pins.lean RBM3D/Propagator/Prop5Short.lean
RBM3D/Propagator/Pins.lean:0
RBM3D/Propagator/Prop5Short.lean:0
$ git diff --stat main...t/T2007; git diff --name-only main...t/T2007 | wc -l
 RBM3D/Propagator/Pins.lean       | 439 +++++++++++++++++++++++++++++++++
 RBM3D/Propagator/Prop5Short.lean | 506 +++++++++++++++++++++++++++++++++++++++
 2 files changed, 945 insertions(+)
       2
```
```
$ lake env lean T2007_names.lean 2>&1 | grep -c error; grep -c "#check" T2007_names.lean   # names of (c)
0
55
```

### Narrative
1. Delivered: `RBM3D/Propagator/Pins.lean` (439 lines) and `RBM3D/Propagator/Prop5Short.lean` (506 lines), two commits on `t/T2007`; `git diff --name-only main...t/T2007` lists exactly these two files. Build, 19 axiom lines, forbidden-token grep, name-clash grep: above.
2. Target 1. The nine pin blocks are identical to the check file and to the probe `d6e6054` (script above). The four bridges (`Prop5Short.thetaDecayShort`, `Prop5Decay.thetaDecay`, `Prop8ZeroMode.thetaZeroMode`, `Prop5Decay.toQ`), `PropThetaQ_Theta_eq`, the three refutations and `Prop5_needs_Lambda` are the probe proofs, verbatim after renaming the private helpers `probe_*` to `pins_*` and `probeAxis` to `pinsAxis` (port script above). The probe's own tests `probeSkeleton`, `probeInst5..8` are not carried over (grep count 0). Added: docstrings, a module docstring, 11 `example` instances in `Pins.lean` (pins of other gates stay hypotheses; the refutations, `PropThetaQ_Theta_eq` and `Prop5_needs_Lambda` are applied at `d = 3`, with `g = 1/2`, `m = I` where the statement has them).
3. Target 2, route S7. `SB = s•1 + (g²s)•Adj` (`P5s_SB_eq`), `s = (1+2dg²)⁻¹`; with `ξ = t·m(σ)²`, `w = 1 - ξs`, `K = (ξg²s/w)•Adj` one has `1 - ξ•SB = w•(1 - K)`, and `Θ = w⁻¹•Σ_k K^k` by the uniqueness lemma `eq_Theta_of_mul` (`P5s_Theta_eq`). Entries: `Adj^k(0,a) = 0` for `k < |a|` (`P5s_adj_pow_eq_zero`); for `k ≥ 1`, `|K^k(0,a)| ≤ 2d|ν|·r^{k-1}` (`P5s_pow_succ_entry_le`, `r ≥ ‖K‖`), with `2d|ν| ≤ 2dg²/κ'` (this is the factor `g²`).
4. Gap and ratio (`P5s_gap_sq`, `P5s_arith`): `|w|² = (1-ts)² + 4ts(Im m)² ≥ κ'²`, `κ' = min κ 1`; `ρ = 2d|ν| = t(1-s)/|w| ≤ r := (1+q)/2` with `q = (1 + 4 s_min κ'²)⁻¹`, `s_min = (1+2dΛ²)⁻¹`. The support indicator is removed by `r = r₂θ`, `r₂ = (1+r)/2`, `θ = r/r₂ < 1`: for `k ≥ |a|`, `r^k ≤ r₂^k θ^{|a|}`, so `Σ_k` is a plain geometric series in `r₂`. Output: `c = -log θ`, `C = κ'⁻¹(1-r₂)⁻¹(1 + 2d/(κ' r))`, depending on `(d, Λ, κ)` only.
5. Relation to (a): (a) takes `ρ₀ = √q` (`c = 0.066766`, `C = 397.257` at `(3,1,1/2)`); the Lean constants use `r = (1+q)/2 ≥ √q` and the second slack `r₂` (`c = 0.032790`, `C = 883.200`, script above). (a)'s constants are valid and sharper; the pin quantifies `∃ C c`, so nothing in (a) is wrong and there is no (a′). The numeric check of the Lean constants (`T2007_const.py`): maximal ratio `|Θ(0,a)|/bound = 0.00113` on the grid listed there.
6. Instance: the two `example`s in `Prop5Short.lean` (printed above) apply `prop5Short_holds 3 1 (1/2)` at `L = 5`, `g = 1/2`, `t = 9/10`, `m = I`, `σ = true`, at `a = 0` and at `a = (1,0,0)` (`≠ 0`, `|a| = 1`, both by `decide`); every hypothesis is discharged by `norm_num`/`Complex.norm_I`. At this data `|Θ(0,0)| = 0.756004`, `|Θ(0,(1,0,0))| = 0.052158` (script), so neither side is trivial.
7. `3 ≤ d` (the first hypothesis of the pin) is not used by the proof (it is introduced as `_`); `L ≥ 3` enters through `card_adj` and `norm_SB`.
8. Consequence for merged code: the example `∀ d g m, ThetaDecayShort d g m` compiles (bridge `Prop5Short.thetaDecayShort` applied to `prop5Short_holds d g m.im`), so the hypotheses `ThetaDecayShort d g m` of `Loop/*` and `Kernel/*` are dischargeable. No merged signature was changed; whether to discharge them is the dispatcher's call.
9. No port from `../RBM1D` or `../RBM2D` (nothing was read from them), so no diff-stat applies; the only source copied is the probe at `d6e6054` (read with `git show`, branch `t/T2003` not checked out).

## (c) Verified Mathlib names
All 55 names below compile as `#check @name` (script output above, 0 errors); no name was found absent.
`Matrix.linfty_opNorm_def`, `Finset.le_sup`, `NNReal.coe_le_coe`, `Finset.sup_le`, `Finset.single_le_sum`, `Finset.sum_filter`, `Finset.sum_const`, `norm_pow_le`, `pow_le_pow_left₀`, `norm_sum_le`, `Matrix.mul_apply`, `pow_succ`, `pow_succ'`, `smul_pow`, `Matrix.smul_apply`, `NormedRing.inverse_one_sub` (states `Ring.inverse (1 - x) = ↑(Units.oneSub x h)⁻¹`; the tsum form follows by `rfl`, as in `Propagator/Basic.lean`), `Units.oneSub`, `Units.val_oneSub`, `Ring.inverse_mul_cancel`, `summable_geometric_of_norm_lt_one`, `Pi.hasSum`, `HasSum.tsum_eq`, `Matrix.smul_mul`, `Matrix.mul_smul`, `inv_mul_cancel₀`, `mul_div_cancel₀`, `div_le_iff₀`, `div_le_div_of_nonneg_left`, `inv_le_one_of_one_le₀`, `inv_anti₀`, `pow_le_pow_of_le_one`, `pow_le_pow_iff_left₀`, `pow_lt_pow_left₀`, `pow_le_one₀`, `mul_le_of_le_one_left`, `tsum_mul_left`, `tsum_geometric_of_lt_one`, `summable_geometric_of_lt_one`, `Summable.mul_left`, `norm_inv`, `norm_div`, `Complex.sq_norm`, `Complex.normSq_apply`, `Complex.norm_real`, `Complex.norm_I`, `Real.exp_nat_mul`, `Real.exp_log`, `Real.log_neg`, `div_lt_one`, `inv_lt_one_of_one_lt₀`, `Matrix.one_apply_ne`; RBM names reused: `card_adj`, `zdistD_add_le`, `norm_SB`, `eq_Theta_of_mul`. Tactic `module` is available. Deprecated in this Mathlib (build warnings seen during writing, absent from the final files): `if_pos`, `if_neg`, `if_true`, `if_false`.

## (d) Open issues and paper-delta candidates
- No new paper-delta candidate. Cited, not re-proposed: T2003a (constants of the pins depend on `(d, Λ)`; `Prop5_needs_Lambda` is the compiled evidence for pin 5; `prop5Short_holds` has `Λ`-dependent constants too), T2003d (`(prop:ThfadC_short)` proved by a gap + Neumann argument without `[bourgade2019random]`; the explicit gap used here is `|1 - tsμ| ≥ min(κ,1)`, a different constant from T2003d's `sin²φ`, constants are not part of the pin).
- The `3 ≤ d` hypothesis of the pin is idle in the proof (item 7). The pin is pinned and was not changed.
- Follow-up for the dispatcher (not done here): discharging `ThetaDecayShort` in the consumers (item 8).
- Nothing blocked; no ticket text, pin, or frozen signature was changed.

## Amend 1 — Sat Oct  3 00:42:30 UTC 2026 (repairer; branch `t/T2007` at 64e6082, parent 29230e9)
Scope: `docs/tickets/T2007.md` Amend 1 (CONTROL H9 (a)); only `RBM3D/Test/Axioms.lean` changed. Pins.lean and Prop5Short.lean unchanged (blob hashes below).
```
$ git diff 29230e9 HEAD -- RBM3D/Test/Axioms.lean
diff --git a/RBM3D/Test/Axioms.lean b/RBM3D/Test/Axioms.lean
index 8d2eae3..a5f611f 100644
--- a/RBM3D/Test/Axioms.lean
+++ b/RBM3D/Test/Axioms.lean
@@ -69,10 +69,14 @@ matters more than the count:
 Reporting them in one list makes "zero axioms" look better than the situation is.
 -/
 
-/-- Premises the **paper** cites rather than proves. -/
+/-- Premises the **paper** cites rather than proves.  The pins of `lem_propTH` properties
+5–8 (T2003, DECISIONS §13) and their KL-local form (T2004, §15) replace the old `ThetaDecay`
+… `PropTH` as the statements route H (DECISIONS §14) discharges; they are not authorised
+external inputs (DECISIONS §5), so they must end up proved. -/
 def borrowedProps : List Name :=
   [`RBM.ThetaDecay, `RBM.ThetaDecayShort, `RBM.ThetaDiffOne, `RBM.ThetaDiffTwo,
-   `RBM.ThetaZeroMode, `RBM.PropTH, `RBM.Loop.KTreeRep]
+   `RBM.ThetaZeroMode, `RBM.PropTH, `RBM.Loop.KTreeRep,
+   `RBM.Prop5Decay, `RBM.Prop8ZeroMode, `RBM.Prop5to8, `RBM.Loop.KLPT]
 
 /-- Premises **this development** owes: provable here, assumed for now.
 
@@ -94,7 +98,12 @@ def structuralProps : List Name :=
    `RBM.Loop.Crossing,        -- two diagonals cross
    `RBM.SameSignOutside,      -- `A ⊇ I_diff(σ)`, the condition of `lem:sum_decay_nonzero`
    `RBM.Graph.Case.Rel,       -- the case relation of `lem_scalingorder`, a parameter
-   `RBM.NormStochDom]         -- `‖A‖ ≺ ζ`: notation of `(stoch_domination)`, not a result
+   `RBM.NormStochDom,         -- `‖A‖ ≺ ζ`: notation of `(stoch_domination)`, not a result
+   `RBM.Gauss.Sizes.WO,       -- `(eq:WO)`: the window of the size sequence
+   `RBM.Gauss.Sizes.Bandwidth, -- `(Main_DEL_COND)`: `W ≥ N^𝔠`
+   `RBM.Gauss.Sizes.SizeTendsto, -- `N → ∞` along the size sequence
+   `RBM.Gauss.Sizes.Admissible, -- the standing hypotheses of the main results
+   `RBM.Gauss.Sizes.locDomain] -- the spectral domain `𝐃_{κ,ε}`
 
 /-- The premises the audit reports on: borrowed plus owed. -/
 def interfaceProps : List Name := borrowedProps ++ owedProps
$ git diff --name-status main...HEAD
A	RBM3D/Propagator/Pins.lean
A	RBM3D/Propagator/Prop5Short.lean
M	RBM3D/Test/Axioms.lean
$ git rev-parse 29230e9:RBM3D/Propagator/{Pins,Prop5Short}.lean HEAD:RBM3D/Propagator/{Pins,Prop5Short}.lean
e10c2bf1f2d17397bb11dd31b42425458ab42098
06a0f608bc6c2060dc490491f9842ab4626516be
e10c2bf1f2d17397bb11dd31b42425458ab42098
06a0f608bc6c2060dc490491f9842ab4626516be
$ lake build 2>&1 | grep -E "axiom audit:|premises found|^registry|Build completed"; echo exit=$?   # branch root, which does not import the two new modules
info: RBM3D.lean:45:0: axiom audit: 510 theorems, 173 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 11 (borrowed 4, owed 1, structural 6).
registry: 11 borrowed + 2 owed + 11 structural; 13 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
Build completed successfully (3254 jobs).
exit=0
$ cat /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2007RootCheck.lean
import RBM3D
import RBM3D.Propagator.Pins
import RBM3D.Propagator.Prop5Short

#assert_rbm_axioms
$ lake env lean <that file> 2>&1 | grep -E "axiom audit:|premises found|^registry|non-vacuity"; echo exit=$?   # root environment plus the two new modules, as at merge
axiom audit: 526 theorems, 183 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 11 (borrowed 4, owed 1, structural 6).
registry: 11 borrowed + 2 owed + 11 structural; 13 registered premise(s) carry nothing yet: [RBM.ThetaDecay,
non-vacuity certificates: 6 of 13 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
exit=0
```
The branch `RBM3D.lean` does not import `Propagator/Pins` and `Propagator/Prop5Short` (root imports are the hub's at merge), so the full `lake build` alone does not exercise the new premises; the scratch file above (not committed) runs the root `#assert_rbm_axioms` with them imported: exit 0, no unregistered premise. Final info line (registry counts): `registry: 11 borrowed + 2 owed + 11 structural`, scan `11 (borrowed 4, owed 1, structural 6)`. `RBM.Loop.KLPT` (T2008) and the five `RBM.Gauss.Sizes.*` (T2006, merged on main after this branch's base 6a555f7) are absent from this branch and are listed as carrying nothing; `Name` literals with a single backtick are not resolved, so their absence does not fail the build.
