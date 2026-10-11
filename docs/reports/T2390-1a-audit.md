Auditor model: claude-opus-5-5

# T2390 1a-audit round 2 (design gate G3a / G3b / G4; Amend 1) — Sat Oct 10 21:57:19 UTC 2026

Inputs: ticket `docs/tickets/T2390.md`; Amend 1 `docs/tickets/T2390-amend-1.md`; `docs/reports/T2390-prove.md` sections (a), (G), (a″), (a′) (262 lines); round-1 audit D1–D4; branch `t/T2390` = `10fcef2`; audit worktree `../RBM3D-wt/T2390-1aaudit2` (detached, `10fcef2`); main = `b53fd22`.
Verdict: **PASS.** D1–D4 are met. No binding stop line is hit. No dispatcher sign-off is needed: Amend 1 item 1 decides D2.

## 1. D1: probe compiled in the audit worktree
```
$ git diff --stat main...t/T2390
 RBM3D/Probe/T2390Pins.lean | 176 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 176 insertions(+)
$ cd ../RBM3D-wt/T2390-1aaudit2 && lake env lean RBM3D/Probe/T2390Pins.lean ; echo EXIT=$?
BAStab : ℕ → (L : ℕ) → [NeZero L] → ℝ → ℝ → ℂ → ℝ → ℝ → Prop
@GreenCore_loopPrem : {d : ℕ} → (sz : Sizes d) → (ℕ → ℂ) → (ℕ → ℝ) → ℝ → ((n : ℕ) → Zd d (sz.L n) → Zd d (sz.L n) → ℝ) → Prop
GreenCore_decayRHS : (d L : ℕ) → ℕ → [NeZero L] → ℝ → ℝ → (Zd d L → Zd d L → ℝ) → ℝ → Zd d L → Zd d L → ℝ
@GreenCore_decayConcl : {d : ℕ} → (sz : Sizes d) → (ℕ → ℂ) → (ℕ → ℝ) → ℝ → ℝ → ℝ → ((n : ℕ) → Zd d (sz.L n) → Zd d (sz.L n) → ℝ) → (ℕ → ℝ) → Prop
BAGbEXPij' : ℕ → Prop
BAGbEXPii : ℕ → Prop  /  BAGbEXPav : ℕ → Prop  /  BAGbEXPij : ℕ → Prop
baBootstrap'_holds : ∀ (d : ℕ), BAFlowMember d → BAGbEXPii d → BAGbEXPij d → BABootstrap' d
baStep1_holds : ∀ (d : ℕ), BAGbEXPii d → BAGbEXPij d → BAStep1 d
SizesInst.sz0_values : SizesInst.sz0.L 0 = 4 ∧ SizesInst.sz0.W 0 = 32 ∧ SizesInst.sz0.size 0 = 2097152 ∧ SizesInst.sz0.lam 0 = 1 / 64
EXIT=0                     (5.6 s; three #check lines joined with "/" here to save space)
$ diff <(sed -n '44,47p;54,59p;64,67p;71,77p;85,96p' RBM3D/Probe/T2390Pins.lean) <(sed -n '185,217p' docs/reports/T2390-prove.md) && echo STATEMENTS_IN_REPORT_MATCH_FILE
STATEMENTS_IN_REPORT_MATCH_FILE
$ grep -nE 'sorry|admit|^axiom| axiom |native_decide' RBM3D/Probe/T2390Pins.lean; echo grep-exit=$?
grep-exit=1
$ grep -c '^theorem\|^lemma' RBM3D/Probe/T2390Pins.lean ; grep -rn "BAGbEXPij'\|GreenCore_\|BAStab" RBM3D (on main) | wc -l
0
       0
```
**Statement of `BAGbEXPij'` against `(GijGEX_BA)` (`7_8:1916-1946`, read in full) and the ticket's (vi):**
- Quantifier order: `∀ κ ε 𝔡 > 0, ∃ c > 0, ∀ 𝔠 sz z, BAFlow → ∀ t ∈ [0, BAflowT0] → ∀ ε₀ > 0, ∀ D > 0, ∀ Φ Ψ`. `t`, `BAFlow`, the carrier and the law are those of the merged `BAGijGEX` / `BAGbEXPij` (`Step1Boot.lean:88-117`).
- Deterministic hypotheses: `0 < Φ ≤ W^{-ε₀}` and `W^{-d/2} ≤ Ψ ≤ W^{-ε₀}`, both `∀ᶠ n`.
- Premise: `1_Ω 𝓛^{(2)}_{(−,+),(a,b)} ≺ Φ(a,b)²`, uniform in `(a,b)`. `![false,true]` is `(−,+)`, the same convention as `STmaxLoop2g` (`Chain/Carrier.lean:135`).
- Conclusion: `1_Ω |(G_t−M)_xy| ≺ Σ_{a',b'} Φ e^{-c(|a'−a|+|b'−b|)} + Ψ e^{-c|a−b|} + W^{-D}` for `x ≠ y` (`zdistInf`).
- No hypothesis is hidden in a structure, and there is no cycle: these are `def`s over merged objects only.
- Differences from the paper:
  - event `1_Ω` on the premise and the conclusion; `(initialGT2)` (`3_5:28-30`) dropped: T2390a;
  - pairs `x ≠ y` only: T2390e;
  - `c` chosen before the sizes: T2390f.
  All are covered.
- `BAStab` is `Stable S ξ K` with the complex kernel `BAMss … true true` (G.2 (S1)); it is G3b's pin.

**Nonempty instances** (compiled above):
- line 120: `BAReal 3 4 0 (1/2) 0 i ∧ BAStab 3 4 0 0 i (1/2) 1`, with every hypothesis proved;
- line 149: positive-coupling `BAReal` data from `flow_sz0`;
- line 160: `BAGbEXPij' 3` applied at `sz0` (`L=4, W=32, N=2097152`), `t ≡ 1/2`, `ε₀=1/10`, `Φ ≡ W^{-1/10}`, `Ψ=W^{-1}`. `BAFlow`, the `t` window, `ε₀`, `D` and the three windows are discharged. The owed pin and `GreenCore_loopPrem` remain hypotheses.
- None of the data is degenerate. Observation O3 concerns the loop premise.

## 2. D2: decided by Amend 1 item 1
The probe does not pin `BAGbEXPii'`, and `BAGbEXPii` is `#check`ed as the stand-in.
- (a′) line 234 records "G.7 per D2: `BAGbEXPii` stands in (T2390d)".
- (a′) line 262 proposes T2390d.
- This covers the round-1 §5 uncovered delta (`max 𝓛` in place of `Ψ_t`, `7_8:1932`).

## 3. Numerics rerun (deliverable (v); round-1 scripts, plus the new `inst.py` and `sz0.py`)
```
$ cp docs/reports/T2390/*.py $SCR/a2/r/ && cd $SCR/a2/r && for s in consts chk; do python3 $s.py > $s.out; diff -q $s.out $R/$s.out && echo "$s IDENTICAL"; done
consts IDENTICAL
chk IDENTICAL
$ python3 stab.py table > stab_table.out; diff -q ... && echo TABLE IDENTICAL; python3 stab.py scan > stab_scan.out; diff -q ... && echo SCAN IDENTICAL
TABLE IDENTICAL
SCAN IDENTICAL
$ diff <(sed -n 1,145p T2390-prove.md) <(sed -n 1,145p T2390-prove.before.md)      # (a)+(G) unchanged since round 1 except one blank line
145d144
$ python3 inst.py      (scratchpad T2390/inst.py; header line omitted)
0.01562 0.5   0.013  4.16e-03 1.29e-32 2.14e-33  64.80  256  16448  7.9  9.42e+01  4096  1.4  8.76e-06  [3.81e-06,8.76e-06] True  128<=4096 True  True  True  True  7.20e-04 True  0.144 True
1      0.25  0.561  2.08e-03 9.89e-38 1.65e-38  64.40  4096  262208  83.3  7.07e+03  16384  1.4  1.26e-06  [4.77e-07,1.26e-06] True  256<=16384 True  True  True  True  1.11e-03 True  0.330 True
10     0.25  4.6723 2.08e-03 9.89e-38 1.65e-38  64.40  4096  262208  642.6  4.13e+05  16384  1.4  1.26e-06  [4.77e-07,1.26e-06] True  256<=16384 True  True  True  True  6.47e-02 True  0.330 True
$ python3 sz0.py
sz0 W=32 g=0.01562: (C1) 8*64*rho_hat*C_th*Phi*delta^2 at delta=W^-3/2 = 286 <= 1: False
sz0 W=32 g=1: (C1) 8*64*rho_hat*C_th*Phi*delta^2 at delta=W^-3/2 = 2.13e+04 <= 1: False
sz0 W=32 g=10: (C1) 8*64*rho_hat*C_th*Phi*delta^2 at delta=W^-3/2 = 1.25e+06 <= 1: False
```
- The values equal the report's (a′) block; the column spacing differs (O2).
- `inst.py`'s `c0` and `mu` are the Lean definitions:
  - `BAct_rate = min(log(1+κ/(4dΛ)), κ/2)` (`CombesThomas.lean:45`);
  - `BAp5s_rate = min(c, (κ²/4)²c/(2AΛ²S))`, `A = 4(BAct_C/c)²`, `BAct_C = 16d²/κ³`, `S = expC(d−2,c)` (`Prop5Short.lean:49-56`, `CombesThomas.lean:42`);
  - `expC` matches `Defs/RadialSum.lean:271`.
- Hence `μ ≤ c₀` holds by definition, and `c_λ = min(c₀/12, μ/6) > 0`.
- The round-1 (v) stop line is still not hit: tables identical, `min gap(1) ≥ 0.988`, `K(1)` saturating in `L`.

## 4. D3: written argument of (a′), re-derived by the auditor
- **D3.1 (m1)** `|G^{(w)}_vy|² ≤ 2|G_vy|² + 8κ⁻²|G_vw|²|G_wy|²` follows from the minor identity and `|G_ww| ≥ κ/2`: correct.
  - (L1): correct.
  - `|ε_w| ≤ 5a`: re-derived as `≤ 2√2 a + 2δ`.
  - `|Q^{XD}_w|`: the LDE sum is over `v ∈ [w]\w`, where `M_vl = 0` (the offsets differ), so the `δ²` bound is right.
  - `C_𝒜 = 7 + 2dg₀(2+32κ⁻²)^{1/2}`: consistent.
- **D3.2 (R1)**
  - `Δ = −GYM` with `M_wy = 1_{o(w)=o(y)}M^{(B)}_{b'c}`.
  - Weighted Cauchy–Schwarz gives the factor `ρ`.
  - The `x`-average of `|M_xy|²` is exactly `W^{-d}|M_ac|²`.
  - Column LDE plus (m1) gives `2𝓛_{(a,b')} + 8κ⁻²δ²R_{a,w}`.
  - All three terms and the constants `2, 8ρΦ_N, 4ρϑ`, `C_ϑ = C_𝒜² + 8κ⁻²` reproduce.
- **Local closure.**
  - `P_{cb'} = 4ρϑ|M_{b'c}|` acts on `c` at fixed `(a,o)`.
  - `Σ_{b'}P_{cb'}e^{ν|c−b'|} ≤ 4ρρ̂ϑ ≤ ½` under (C1), which gives `(ΣP^k)_{cb'} ≤ 2e^{-ν|c−b'|}`.
  - The triangle splits for `(R*)` (`2c₀ = 4ν`) check, and so does `C_R`.
  - The absorbed term is written out and is local. The round-1 `sup R` defect is removed.
- **D3.3 (X*)**
  - `R̃_u ≤ R_{a,(a,o)}`.
  - The cross term uses `e^{-ν|a−b'|/2 − c₀|a−c|} ≤ e^{-ν|c−b'|/2}` (`c₀ ≥ ν/2`).
  - The coefficient `√8/(κc₀)·√C_R` is ≤ `√(2C_R)·2/(κc₀)`.
  - The `Δ`-part is `(√8/κ)a|Δ_uy| ≤ (3/κ)a|Δ_uy|`.
- **D3.4**
  - The expansion `Δ = L1+L2+L3+Q` from (E0), (E1) and `G = M+Δ` is correct. `v̄ = Θ_t u` because `L3_kk = t(M^{(++)}v̄)_a`.
  - Rates: 𝔗 is preserved under `M` for `c ≤ c₀/2`. For L3 the exponent `≥ 3c_λ·(triangle bound)` needs `c_λ ≤ c₀/12` and `6c_λ ≤ μ`, which gives `c_λ = min(c₀/12, μ/6)`. The leftover `2c_λ` makes the `(a',b')` sums finite.
  - Absorption: (C2) `η(ρ̂ + ρ̂²c₀⁻¹C_Θ̂) ≤ ½`, with `C_Θ̂` covering `e^{2c_λ|b−a'|}`, since `2c_λ ≤ μ/3`.
  - `𝒩 < ∞` because `Φ > 0`.
  - (C1) and (C2) are eventual in `n` because `Φ_Nδ² = N^τW^{-2ε₀} → 0` (`τ < 𝔠ε₀`). Their constants depend only on `(d,κ,𝔡)`.
- **Signatures used** (main `b53fd22`):
  - `BAMfine_decay` (`GreenSchur.lean:124`) and `BAMB_decay_large` (`CombesThomas.lean:509`) have the form `≤ c₀⁻¹e^{-c₀ zdistD}`;
  - `BAsum_exp_decay_le` (`Prop5Short.lean:251`, `2 ≤ d`);
  - `BAMfine_norm_le_one` (`GreenSchur.lean:105`);
  - `baProp5s_holds` (`Prop5Short.lean:667`) → `BAProp5s` (`FlowPins.lean:184`): `‖BATheta … t σ σ 0 a‖ ≤ C(1_{a=0} + g²e^{-c·zdistD a})`, for `t < 1`, `g ≤ Λ`, `3 ≤ L`. This bounds row 0 only, so translation invariance is needed. The report assigns it to G3b, and G4 depends on G3b.
- **C1:** no step uses `g ≤ W^{-ε}`, smallness of `‖M − m₀I‖`, or `(Cλ)^{|a−b|}`. `ρ = L^d = 64` appears only in the concrete `L=4` instance, never in the argument.

## 5. D4: instance plan for G3a's endpoints
- Data: `t = 1/2 > 0` (`half_lt_t0`, `FlowPins.lean:1254`, at `sz0`, `g = 1/64`).
- `Δ = δ·E` with `‖Δ‖_max = δ ≠ 0`.
- Explicit numbers at `g = 1/64`: `K_BA = 16448`, `ρ = 64`, `ρ₂ ≤ 1`, `δ = 4096^{-1.4} = 8.76e-6`, `Kδ = 0.144 ≤ ½`, (C1) `= 7.2e-4 ≤ 1` (rerun, §3). Nothing degenerate.
- `BALDEin` is discharged by the merged `baLDEin_holds` (`GreenLDE.lean:199`; `theorem baLDEin_holds (d : ℕ) : BALDEin d`, unconditional).
- Other gates' pins kept as hypotheses: `BAStab` (G3b); the owed `BAGbEXPij'`.
- `sz0.py` shows honestly that the closure fails at `W = 32`, so R3/R4 use a larger numeric `W`. This is allowed: the rows are deterministic in `W`.

## 6. Paper deltas
T2390a–g are proposed in (G.9), (a″) and (a′); d, e, f and g are new in this round. Every Lean/paper difference found in §1 and §4 is covered: event form, dropped `(initialGT2)`, `x ≠ y`, order of `c`, `max𝓛` right side of `BAGbEXPii`, the rate formula and the unused `W^{-D}`.

## 7. Per-deliverable verdict
| item | verdict |
|---|---|
| (i) stability | PASS (round 1, unchanged) |
| (ii) entrywise / minors | PASS (D3.1–D3.3) |
| (iii) off-diagonal decay | PASS (D3.4) |
| (iv) constants | PASS |
| (v) numerics | PASS (reproduced; stop line not hit) |
| (vi) primed pins compiled | PASS (D1; D2 per Amend 1) |
| (vii) split / 1b scope | PASS (D4; G3a 800/1300/1950 < stop line 2000) |

## 8. Observations (no RETURN)
- **O1.** `inst.py` and `sz0.py` are not under `docs/reports/T2390/`, the ticket's script location. They exist only in the session scratchpad (`…/scratchpad/T2390/`), and the report cites them without a path. The auditor reran them from there. Copy them into `docs/reports/T2390/` with their `.out` files before the scratchpad is cleared.
- **O2.** The pasted `inst.py` output (prove report line 253 ff.) has wider column spacing than the rerun. Every number is identical.
- **O3.** `GreenCore_loopPrem` at the line-160 data is surely satisfied:
  - on `Ω`, `𝓛^{(2)}_{(a,b)} ≤ 2W^{-d}max|M^{(B)}|² + 2δ² ≤ 4W^{-2ε₀} = 4Φ²` (`ε₀ ≤ d/2`);
  - so the premise is non-vacuous, and 1b's R5 instance could discharge it rather than assume it.
- **O4.** D4's `𝒦 := M⁻¹Δ − 𝒮[Δ]M` needs the fine `M` to be invertible. This holds, since `M^{(B)} = (g₀Ψ − E − m)⁻¹` with `Im m > 0`. 1b must prove it, or take `(Δ, 𝒦)` from R1's resolvent data instead.
- **O5.** The audit worktree `../RBM3D-wt/T2390-1aaudit2` (detached `10fcef2`) is left in place for the hub.
