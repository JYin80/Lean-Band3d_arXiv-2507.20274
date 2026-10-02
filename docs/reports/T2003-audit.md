Auditor model: claude-opus-5-5

# T2003 audit, round 1 (Fri Oct  2 22:56:59 UTC 2026)
Ticket `docs/tickets/T2003.md` (report-only design, PT-D1). Branch `t/T2003` @ d6e6054, audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2003-audit1` (detached). Prove report `docs/reports/T2003-prove.md` (299 lines).
Lean targets: pins `Prop5Decay`, `Prop5Short`, `Prop6Diff1`, `Prop7Diff2`, `Prop8ZeroMode`, bundle `Prop5to8` (item 2), skeleton `probeSkeleton` (item 4), instances `probeInst5/5s/6/7/8` (item 5). Items 1, 3, 6, 7 are report content.

## 1. Build, axioms, forbidden tokens, diff scope
```
$ git diff --name-status main...t/T2003 ; git diff main...t/T2003 -- RBM3D.lean RBM3D/Propagator | wc -l
A	RBM3D/Probe/T2003Pins.lean
       0
$ lake build RBM3D.Probe.T2003Pins 2>&1 | grep -E '^(warning|error)|Build completed|rror'
Build completed successfully (2432 jobs).
$ grep -nE 'sorry|admit|native_decide|^\s*axiom ' RBM3D/Probe/T2003Pins.lean | wc -l
       0
$ lake env lean RBM3D/Probe/T2003Pins.lean 2>&1 | awk '/depends on axioms/{n++; if(index($0,"[propext, Classical.choice, Quot.sound]"))s++; next}{o++; print}END{print "axiom lines:",n,"standard-only:",s,"other lines:",o+0}'
axiom lines: 25 standard-only: 25 other lines: 0
```
Only the sole writable Lean file is touched; no frozen signature changed. Report-only: per the ticket the probe stays on the branch (hub rule (A): skip steps 3-5; merge only the reports).

## 2. Statements against `lem_propTH` (`1_2_Intro_model_result.tex:1068-1185`), line by line
Definitions the pins use (read from the files):
```
Defs/Params.lean:32  ellT L g t   := min (max (g / Real.sqrt |1 - t|) 1) L                        = (eq:ellt)
Defs/Params.lean:36  Bparam d L g t K := (g^2+|1-t|)⁻¹ * ((K+1)^(d-2))⁻¹ + (L^d*|1-t|)⁻¹           = (eq_B_param)
Defs/Block.lean:38   sbKernel: 0 ↦ (1+2dg²)⁻¹, |x|=1 ↦ g²(1+2dg²)⁻¹, else 0; SB = circulant          = (eq:variancematrix)
Propagator/Basic.lean:70  Theta d L g ξ = Ring.inverse (1 - ξ • SB d L g)                           = (def_Thxi), M = m(σ1)m(σ2) I
Propagator/Basic.lean:225 Theta0 = Θ_ab - L^{-2d} Σ_{a'b'} Θ_{a'b'}                                 = (def_Thxi0)
Probe:28  PropSpin m σ = if σ then m else conj m                                                     = (def_mtzk)
```
| item | paper | pin | verdict |
|---|---|---|---|
| order | ∃ c_d, C_d (dep. d) ∀ a | `3≤d → 0<Λ → ∃C>0 ∃c>0 ∀L≥3 ∀g∈(0,Λ] ∀t∈[0,1) ∀m (‖m‖=1) ∀σ1 σ2 ∀a` | constants before L, g, t, m, σ, a: OK (uniform in σ: stronger, finite set) |
| λ range | `(eq:WO)`: λ ≤ 𝔡⁻¹ | `0 < g ≤ Λ`, never a fixed λ | OK; constants on (d,Λ): delta T2003a, necessity compiled (`Prop5_needs_Lambda`) |
| P5 | `C_d B_{t,|a|} e^{-c_d|a|/ℓ_t}` | `C * Bparam d L g t |a| * exp(-c|a|/ellT L g t)` | literal match; all unit m (paper: bulk m): stronger, T2003e |
| P5s | σ1=σ2: `C_κ(1_{a=0} + λ² e^{-c_κ|a|})`, (d,κ) | `σ1=σ2=σ`, `κ ≤ Im m`, `C((if a=0 then 1 else 0) + g² exp(-c|a|))`, (d,Λ,κ) | match; bulk as `κ ≤ Im m`: T2003d |
| P6 | `|r| ≲ |a|`, `≺ (λ²+|1-t|)⁻¹|r|(|a|+1)^{1-d}` | `|r| ≤ c|a|`, `0<c<1`, no loss, `C(g²+|1-t|)⁻¹|r|((|a|+1)^(d-1))⁻¹` | c<1 forced (c=1 false: `Prop6Old_false`), T2003b; no loss = stronger, T2003c |
| P7 | `≺ (λ²+|1-t|)⁻¹|r|²(|a|+1)^{-d}` | same form, `|r|²`, `((|a|+1)^d)⁻¹` | as P6 (`Prop7Old_false`) |
| P8 | `|Θ̊(0,a)| ≺ (λ²+|1-t|)⁻¹(|a|+1)^{2-d}` | `‖Theta0 … 0 a‖ ≤ C(g²+|1-t|)⁻¹((|a|+1)^(d-2))⁻¹`, no loss | match; stronger (no loss), T2003c |
| |a| | paper `|a|` | `zdistD` (periodic ℓ¹) | T2003f |
Non-vacuity of the RHS/LHS: `t<1`, `‖SB‖=1` ⇒ `1-ξ•SB` invertible, so `Ring.inverse` is the true inverse (no junk 0); every RHS factor is positive (`ellT ≥ 1` for L ≥ 3). `Prop5to8` is the bundle of the pins themselves (not a hidden hypothesis); no circular dependency (pins are `Prop`s; nothing assumes them except the skeleton/instances). `d - 2`, `d - 1` are ℕ-subtraction, exact for d ≥ 3.

## 3. Extreme inputs (TEAM §8 lesson 25), auditor's own script (FFT on the torus, d = 3)
Θ(0,a) = L^{-d} Σ_k e^{ik·a}/(1 - ξŜ(k)), Ŝ(k) = (1+2g²Σcos k_j)/(1+2dg²); Θ̊ = Θ - L^{-d}/(1-ξ). Sweep: g ∈ {1, 0.01} (λ = Λ and λ → 0), e = 1-t ∈ {1, g², g²/L², 0.1g²/L³, 1e-10} (t → 1), μ ∈ {1, -1 (m=i), e^{2iπ/3} (m=e^{iπ/3})}, L ∈ {8, 9, 17, 33, 65} (L large); ratio = LHS / (pin RHS without C); P5 c=0.3 (entries below 1e-11·max masked), P5s c=0.05, P6/P7 c=1/2 with r ∈ {(1,0,0),(0,1,0),(1,1,0),(2,0,0),(1,1,1),(3,0,0),(2,2,0)}, all a with |r| ≤ |a|/2.
```
$ python3 aud2003.py 8 9 17 33 65      # auditor scratchpad; run before 22:56:59 UTC; 12.6 s wall
P5   g=0.01  sup over e,mu by L: L=8:1.568  L=9:1.492  L=17:1.527  L=33:1.546  L=65:1.556
P5   g=1.0   sup over e,mu by L: L=8:1.992  L=9:1.995  L=17:1.999  L=33:2.000  L=65:2.000
P5s  g=0.01  sup over e,mu by L: L=8:1.000  L=9:1.000  L=17:1.000  L=33:1.000  L=65:1.000
P5s  g=1.0   sup over e,mu by L: L=8:0.500  L=9:0.500  L=17:0.500  L=33:0.500  L=65:0.500
P6   g=0.01  sup over e,mu by L: L=8:0.454  L=9:0.454  L=17:0.454  L=33:0.454  L=65:0.454
P6   g=1.0   sup over e,mu by L: L=8:2.652  L=9:2.673  L=17:2.764  L=33:2.817  L=65:2.824
P7   g=0.01  sup over e,mu by L: L=8:1.431  L=9:1.154  L=17:1.077  L=33:1.092  L=65:1.108
P7   g=1.0   sup over e,mu by L: L=8:10.012  L=9:8.076  L=17:7.421  L=33:7.639  L=65:7.754
P8   g=0.01  sup over e,mu by L: L=8:0.998  L=9:0.999  L=17:1.000  L=33:1.000  L=65:1.000
P8   g=1.0   sup over e,mu by L: L=8:1.996  L=9:1.997  L=17:2.000  L=33:2.000  L=65:2.000
```
Every ratio is bounded and flat in L, in λ → 0 and in t → 1 (e = 1e-10 included); no pin is false at an extreme input. The numbers agree with the prove report (P6 2.82, P7 7.75 at L=65; P7 10.01 at L=8, report (a′) item 3). Analytic sanity (auditor): for e ≥ λ² the walk bound Θ(0,a) ≤ (tp)^{|a|}/(e+tp)^{|a|+1}, p = 2dλ²/(1+2dλ²), gives ratio ≤ 2d/(2d+1) uniformly in λ, consistent with a λ-uniform c_d; for d ≥ 3 the heat-kernel integrals ∫ e^{-es}∇^jK_s ds converge without logarithms, consistent with the loss-free P6-P8.

## 4. Compiled nonempty instances
In the probe (b3 of the prove report, re-read in the file, lines 160-225): `probeInst5`, `probeInst5s`, `probeInst6`, `probeInst7`, `probeInst8` apply each pin at d=3, L=5, g=1/2, t=9/10, Λ=1, κ=c=1/2, m ∈ {i, e^{iπ/3}} (`probe_re_ne`: Re i = 0, Re e^{iπ/3} ≠ 0), all sign pairs, a=(2,0,0), r=(1,0,0) (`probe_dist_ra`: |r| = 1 ≤ ½·2, by `decide`). The pin is a hypothesis (unproved gate pin, allowed); every deterministic hypothesis (3≤3, 0<1, 0<κ, 0<c<1, 3≤5, 0<1/2≤1, 0≤9/10<1, ‖m‖=1, κ≤Im m, |r|≤c|a|) is discharged. Nondegenerate (125 sites, a ≠ 0, r ≠ 0, t > 0, g > 0). `probeSkeleton` (item 4) derives `‖Θ_{t₀}(0,0)‖ ≤ C·B_{t₀,0}` from `Prop5to8`, constants before L, g, t₀.
Auditor's extra check (scratch file outside the tree, no source edit), applying the public supporting theorems and the bundle at concrete data:
```
$ cat AudT2003.lean | grep -E '^example'
example : ¬ ThetaDiffOne 3 1 1 := Prop6Old_false 3 le_rfl 1 one_pos 1 (by simp)
example : ¬ ThetaDiffTwo 3 1 1 := Prop7Old_false 3 le_rfl 1 one_pos 1 (by simp)
example : ¬ PropTH 3 1 1 := PropTH_false 3 le_rfl 1 one_pos 1 (by simp)
example := Prop5_needs_Lambda 3 (by norm_num)
example (h : Prop5to8 3 1 (1/2) (1/2)) : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ‖Theta 3 5 (1/2) (((9/10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false)) 0 0‖ ≤ … := …
$ lake env lean AudT2003.lean; echo exit=$?
exit=0
```
The merged `ThetaDiffOne`/`ThetaDiffTwo`/`PropTH` (`Interface.lean:118-176`, `∀ c > 0`) are refuted in Lean; prove report b6 shows no merged file takes them as a hypothesis.

## 5. Item 1 spot check (RBM2D at c9a24cf, read-only)
```
$ git -C ../RBM2D --no-optional-locks ls-tree --name-only c9a24cf RBM2D/Propagator/ | wc -l ; git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Propagator/Prop5.lean | wc -l ; grep -E '^\(c\) +Prop5 ' RBM3D/Probe/T2003Pins.lean
      87
     178
(c)    Prop5                                        178    1/13         -        final P5: 180*40002^2 (1+log L), no polynomial prefactor (d-2=0)
```

## 6. Paper-delta coverage
Every Lean/paper difference found in §2 has a candidate in prove report (d): T2003a (constants on (d,Λ)), T2003b (|r| ≤ c|a|, 0<c<1), T2003c (no loss in 6-8), T2003d (bulk as κ ≤ Im m; gap-based 5s), T2003e (P5 for every unit m), T2003f (periodic ℓ¹ |a|). Old D11 kept, D12, D13 superseded (with compiled evidence for D12).

## 7. Verdicts
| target | verdict |
|---|---|
| `Prop5Decay` (prop:ThfadC) | PASS |
| `Prop5Short` (prop:ThfadC_short) | PASS |
| `Prop6Diff1` (prop:BD1) | PASS |
| `Prop7Diff2` (prop:BD2) | PASS |
| `Prop8ZeroMode` (prop:ThfadC0) | PASS |
| `Prop5to8`, `probeSkeleton` (item 4) | PASS |
| instances `probeInst5/5s/6/7/8` (item 5) | PASS |
| items 1, 3, 6, 7 (report) | PASS (content delivered; see sign-off) |

**Overall: PASS — needs dispatcher sign-off** on one point that is not a statement defect: the chosen route H (Poissonised heat-kernel route, items 3 and 7) is neither RBM2D's route nor the paper's Fourier summation by parts; DECISIONS §7 ("改路线 … 报 Jun，不自行换") makes this a route-level decision for Jun before PT proof tickets are cut from the split table. The pins themselves are route-independent.

## 8. Observations (no effect on statements, instances, build, axioms or delta coverage)
- O1. The bulk clause `κ ≤ Im m` is also carried by P6, P7, P8 (idle for σ1 ≠ σ2); the paper's lemma states 6-8 without it (bulk is fixed by context). Suggest T2003d's wording name P6-P8 explicitly.
- O2. Prove report section (a) cites scratch-directory scripts under `/private/tmp/...` that do not persist; the sources are reproduced in probe Appendix C, so the evidence remains available on the branch.
- O3. The pins prove nothing yet; P5-P8 rest on numerics (reproduced in §3) and the route sketch, as the report itself states. The route-H pilot (tickets B1+B2) is where it can fail; fallback F is priced.
- O4. Report-only ticket: at merge the hub must not bring `RBM3D/Probe/T2003Pins.lean` into `main` or add a root import (ticket: "probe stays on branch").
