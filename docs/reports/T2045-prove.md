Prover model: claude-sonnet-5-5
## (a) Math preflight — Sat Oct  3 10:26:33 UTC 2026

Notation: `x = 1-t`, `g = lam_n` (the paper's ilambda), `a_t = Bctl n t = W^{-d} B_{t,0}` with
`B_{t,0} = (g²+x)^{-1} + (L^d x)^{-1}` (1_2:1108), `ℓ_t = min(max(g x^{-1/2},1),L)` (1_2:1121), `N=(WL)^d`,
`η_t = x·Im m(E)`. Constants: `𝔠` (W ≥ N^𝔠), `𝔡` ((eq:WO): W^{-d/2+𝔡} ≤ g ≤ 𝔡^{-1}), `τ` (RangeCond: x ≥ N^{-1+τ}), `𝔠_d ≤ 1/100` (con_st_ind, 1_2:1296).

### (i) Exponent table

Regimes at general d ≥ 3 (x = 1-t; a fourth regime x ≤ g²/L^d is nonempty and must be handled by every fact):

| regime | ℓ² | B_{t,0} (bounds) | a_t | RBM2D (c9a24cf, `Path/Scales.lean`, g=1, M=W²ℓ²η) |
|---|---|---|---|---|
| 1: x ≥ g² | 1 | [1/(2x), (1+L^{-d})/x] | ≍ 1/(W^d x) | RBM2D ℓ_u = min(x^{-1/2},L) = merged ℓ at g=1 for 0≤u<1, so x ≤ 1 = g²: regime 1 only at x=1 |
| 2: g²/L² ≤ x ≤ g² | g²/x | ≍ 1/g² | ≍ 1/(g²W^d) (plateau) | ℓ²=1/x, M=W² Im m (plateau) |
| 3: g²/L^d ≤ x ≤ g²/L² | L² | ≍ 1/g² (1/(L^d x) ≤ 1/g²) | ≍ 1/(g²W^d) (plateau) | none (g=1, d=2: g²/L^d = g²/L², regime empty) |
| 4: x ≤ g²/L^d | L² | ≍ 1/(L^d x) | ≍ 1/(N x) | x ≤ L^{-2}: M = N x Im m, M⁻¹ ≍ 1/(N x) |

| # | quantity | RBM2D value | d ≥ 3 value | constraint / slack |
|---|---|---|---|---|
| 1 | `B ℓ² x` (all regimes) | M = W²ℓ²η = W² Im m·ℓ²x, so M⁻¹·Im m = (W² ℓ² x)⁻¹ | `B ℓ² x ≤ 2` for all x>0: ℓ² ≤ g²/x+1 gives ℓ²/(g²+x) ≤ 1/x; ℓ ≤ L gives ℓ²/(L^d x) ≤ L^{2-d}/x ≤ 1/x | uses d ≥ 2; slack L^{2-d} ≤ 1/L (3D): `ℓ²xB = ℓ²x/(g²+x)+ℓ²/L^d`, regime 4 ≈ L²x/g²+L^{2-d}. for d=2 (L^{2-d}=1) the term ℓ²/L^d is ≍ 1, so B ≍ 1/(ℓ²x) there; for d ≥ 3 it is not, so the scale is `Bctl` and not 1/(W^dℓ²η) |
| 2 | R1 exponent `c₀` in `a_u ≤ 2N^{-c₀}`, u ≤ t | `Im m·N^{min(2c,τ)} ≤ M_u` (W² ≥ N^{2c}) | `c₀ = min(2𝔠𝔡, τ)`: `a_u ≤ (g²W^d)^{-1} + (N x_u)^{-1} ≤ W^{-2𝔡} + N^{-τ} ≤ 2N^{-c₀}` | needs hyp `sz.WO 𝔡` in addition (g²W^d ≥ W^{2𝔡}, merged `Sizes.lam_sq_mul_pow_ge`), W ≥ N^𝔠, x_u ≥ x_t ≥ N^{-1+τ}. Without WO false: lam ≡ 0, W=L=N^{1/(2d)}, x=N^{-1+τ}, τ=1/10: a ≥ 1/(W^d x) = L^d N^{-τ} = N^{0.4} → ∞. `2N^{-c₀} ≤ 1` iff N ≥ 2^{1/c₀} |
| 3 | R2: step exponent / conclusion | `M_s⁻¹ ≤ (x_t/x_s)^{30}` ⇒ `M_s^{29/30} ≤ M_u` | con_st_ind `a_t^{c} ≤ x_t/x_s` (c = 𝔠_d) ⇒ `a_u ≤ a_s^{1-c}` (a = M⁻¹-role; c=1/30 reproduces 29/30) | needs `a_s ≤ a_t` (row 5) and `x_s/x_u ≤ x_s/x_t`; c ≤ 1/100: exponent ≥ 99/100 > 29/30; chain: a_u ≤ a_s x_s/x_u ≤ a_s·a_t^{-c} ≤ a_s^{1-c} |
| 4 | ratio facts (ScaleFacts:136, :148) | `ℓ_u/ℓ_s ≤ (x_s/x_u)^{1/2}`, `(ℓ_t/ℓ_s)^4 ≤ (η_s/η_t)^2` | same exponents 1/2, 4·(1/2)=2: dimension-free, g-free; `η_s/η_t = x_s/x_t` needs \|E\|<2 | hyp `0 ≤ s` of RBM2D not needed (merged ℓ ≥ 1 via max(·,1)); `0 ≤ g` as merged `ellT_mono`. Sharp: equality at u=t when s,u in regime 2 (script: max ratio 1, attained at s=u=t). Derivation: h(x)=max(g x^{-1/2},1), h(x_u)/h(x_s) ≤ (x_s/x_u)^{1/2} by cases h(x_s)=1 or g/√x_s; min with L keeps it |
| 5 | probe 4.1 row 10: `a_s ≤ a_u`; sharper `x_u a_u ≤ x_s a_s` (s ≤ u < 1) | M anti-ratio (F2) `M_s x_v/x_s ≤ M_v` | `x·B_{x,0} = x/(g²+x) + L^{-d}` nondecreasing in x | exact monotonicity, no slack needed; row 11: `a_s ≥ W^{-d}(g²+1)^{-1}` for 0 ≤ s |
| 6 | closure (probe row 12) | exponent 30 | `a_s x_s/x_u ≤ a_s^{1-c}` (a_s ≤ a_t, a_t^c ≤ x_t/x_s, x_t ≤ x_u); `a^{1-c} ≤ (a^{3/8})²` | needs 0<a ≤ 1, c ≤ 1/4: slack c=1/100 → exponent (1-c)/2 = 0.495 vs 3/8 |
| 7 | R3 form `ℓ_u/ℓ_s ≤ a^{-c/2}` | `M_s^{1/60}` | `(x_s/x_t)^{1/2} ≤ a_t^{-c/2} ≤ a_s^{-c/2}`; c=1/30 gives 1/60, c=1/100 gives 1/200 | from con_st_ind and row 5 |
| 8 | forbidden_region: ε / 2 | threshold `6M_s^{-7/15}` vs `M_s^{-1/4}` (Step1:1024) | α = a_s^{1/4}, f = α^{3/2} = a_s^{3/8}, a = α, b = 2α; hfa: `f ≤ N^{-ε}α` ⇔ a_s^{1/8} ≤ N^{-ε}. From row 2: any ε < c₀/8 eventually (c₀=1/30: ε < 1/240); proof step `N^{ε/2}f ≤ N^{ε/2-ε}a < a` needs size ≥ 2 | pure real/`size : ℕ→ℕ` statement, dimension-free; hsize: `Tendsto sz.size` (SizeTendsto). Instance: pointwise check of `f ≤ N^{-ε}α` with the actual a_s at ε = 1/100 |
| 9 | stepOneBootstrap | none | none (a ≤ b: α ≤ 2α; a continuous: α depends on s only; hsize) | dimension-free |
| 10 | PerTimeCalc thresholds | `2N^{-(D+1)} ≤ N^{-D}` (size ≥ 2), `C ≤ N^{τ'}` | identical with `N := sz.size n = (WL)^d` | size ≥ 2 eventually from hsize |

Dropped (class c / no 3D analogue; to be confirmed against the portmap in 1b): `ChainStepCond`, `chainStepCond`, `scaleFacts_R2` (sequence form via RBM2D `CondStInd`, `chainTime`, `RangeCond` of the 1-2:989 chain; the 3D paper has no such chain, and `STConStInd` plays the role: R2 is stated at `STConStInd` instead), `scaleFacts_inv_sq_le_tailT` (uses `tailT`, `ellStar`, `scaleM`; grep of `RBM3D/` outside Probe: no such defs). Re-stated: R1, R2_pt (via closure), the ratio facts, the checks.

### (ii) One nondegenerate instance (d=3, `sz0` of `RBM3D/Defs/Sizes.lean`: L=4(n+1), W=(2(n+1))^5, lam=(2(n+1))^{-6}, N=(WL)^3)
Constants 𝔠=1/6, 𝔡=1/10, τ=1/10, 𝔠_d=1/100, E=1/2 (|E|<2, Im m=√(4-E²)/2). Five times per n across regimes 1,1,2,3,4 (x = 1, 1/2, g²/L, g²/L^{5/2}, geometric mean of N^{-1+τ} and g²/L^d), all pairs s ≤ u ≤ t.
Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2045/chk.py` (exit 0). Output:
```
n=0: L=4 W=32 lam=0.015625 N=2.09715e+06  g2=0.0002441 g2/L2=1.526e-05 g2/L^3=3.815e-06 N^(-1+tau)=2.044e-06
 hyps: {'bandwidth': True, 'WO': True, 'g2Wd_ge_W2d': True, 'size_ge2': True}
 x=1-t | regime | ell | Bctl | 1/(g2 W^d) | 1/(N x) | B*ell^2*x | x>=N^(-1+tau)
  1 | 1 | 1 | 3.099e-05 | 0.125 | 4.768e-07 | 1.015 | True
  0.5 | 1 | 1 | 6.196e-05 | 0.125 | 9.537e-07 | 1.015 | True
  6.104e-05 | 2 | 2 | 0.1078 | 0.125 | 0.007812 | 0.8625 | True
  7.629e-06 | 3 | 4 | 0.1837 | 0.125 | 0.0625 | 0.7348 | True
  2.793e-06 | 4 | 4 | 0.2943 | 0.125 | 0.1708 | 0.4309 | True
 regimes covered: [1, 2, 3, 4]
 R1: max Bctl=0.2943 <= W^-2d+max 1/(Nx)=0.6708 (True); 2N^-c0=1.231 (c0=0.03333, holds=True, 2N^-c0<=1:False)
 ratio triples=35: max (l_u/l_s)/(x_s/x_t)^(1/2)=1<=1 ; max (l_t/l_s)^4/(eta_s/eta_t)^2=1<=1 ; Bctl mono/xmono/ge: True
 s: x_s | a_s | con_st_ind a_t^c<=x_t/x_s<1 | max_u a_u/a_s^(1-c) | max_u (a_s x_s/x_u)^(1/2)/a_s^(3/8) | forb f<=N^-eps a (eps=1/100): f/(N^-eps a)
  1 | 3.099e-05 | True | 0.9105 | 0.2745 | 0.3159 ; a=alpha<=b=2alpha: True, a_s<=1:True
  0.5 | 6.196e-05 | True | 0.9168 | 0.2994 | 0.3445 ; a=alpha<=b=2alpha: True, a_s<=1:True
  6.104e-05 | 0.1078 | True | 0.9805 | 0.7608 | 0.8756 ; a=alpha<=b=2alpha: True, a_s<=1:True
  7.629e-06 | 0.1837 | True | 0.9868 | 0.8132 | 0.9359 ; a=alpha<=b=2alpha: True, a_s<=1:True
  2.793e-06 | 0.2943 | True | 0.9937 | 0.8626 | 0.9927 ; a=alpha<=b=2alpha: True, a_s<=1:True
 all-checks-ok: True
n=6: L=28 W=537824 lam=1.3281e-07 N=3.41503e+21  g2=1.764e-14 g2/L2=2.25e-17 g2/L^3=8.035e-19 N^(-1+tau)=4.168e-20
 hyps: {'bandwidth': True, 'WO': True, 'g2Wd_ge_W2d': True, 'size_ge2': True}
 regimes covered: [1, 2, 3, 4]
 R1: max Bctl=0.001964 <= W^-2d+max 1/(Nx)=0.07303 (True); 2N^-c0=0.383 (c0=0.03333, holds=True, 2N^-c0<=1:True)
 ratio triples=35: max (l_u/l_s)/(x_s/x_t)^(1/2)=1<=1 ; max (l_t/l_s)^4/(eta_s/eta_t)^2=1<=1 ; Bctl mono/xmono/ge: True
 all-checks-ok: True
OVERALL True
```
Reading: hyps = Bandwidth(1/6), WO(1/10), g²W^d ≥ W^{2𝔡}, N ≥ 2 all True at n=0 and n=6; `2N^{-c₀} ≤ 1` fails at n=0 (1.231) and holds at n=6 (0.383): R1 is an "eventually" statement (first n with N ≥ 2^{30}: N_n = 2^{21}(n+1)^{18}, n ≥ 1). Columns "max_u a_u/a_s^{1-c}", "(a_s x_s/x_u)^{1/2}/a_s^{3/8}", "f/(N^{-ε}a)" are ≤ 1 (rows 3, 6, 8); con_st_ind holds at c=1/100 with x_t = 0.99 x_s. No external hypothesis is used by these targets (the PT/KL pins are not hypotheses here).

### Verdicts
- scaleFacts_R1: PASS, in the form `a_u ≤ 2N^{-min(2𝔠𝔡,τ)}` with the extra hypothesis `sz.WO 𝔡`; the RBM2D `M_u ≥ Im m·N^{c₀}` form has no d ≥ 3 reading (row 1).
- scaleFacts_R2_pt: PASS, in the closure form `a_u ≤ a_s^{1-c}` (row 3).
- scaleFacts_ellT_ratio, scaleFacts_ellT_pow_four: PASS (rows 4; exponents unchanged).
- forbidden_region, stepOneBootstrap: PASS (rows 8-9, dimension-free).
- probe 4.1 closure and monotonicity: PASS (rows 5-6).
Paper-delta candidates for 1b: T2045a (R1 needs WO; `0 ≤ s` dropped), T2045b (dropped chain declarations).

### (a′) Preflight corrections — Sat Oct  3 12:58:25 UTC 2026
No verdict of (a) changes: all verdicts PASS stand.  Two corrections of wording:
- Row 4 lists `0 ≤ g` as needed "as merged `ellT_mono`": `scaleFacts_ellT_mono_ratio` compiles with no sign hypothesis on `g` or `s` (b.4), so the ratio facts need neither `0 ≤ s` nor `0 ≤ g`.
- "Dropped ... to be confirmed against the portmap in 1b": the portmap does not mark `ChainStepCond`, `chainStepCond`, `scaleFacts_inv_sq_le_tailT` unused (its 312 kept lines are the code lines of the RBM2D file, b.9); they are dropped for the reasons in (d), not by the portmap.  `scaleFacts_R2` is kept, at `STConStInd` (b.4).

## (b) Script output
Branch `t/T2045`, commit `60dac4a T2045: S1-08 port Induction/ScaleFacts and Induction/PerTimeCalc (scale facts at d >= 3, forbidden region, Step 1 bootstrap)` (only `RBM3D/Induction/ScaleFacts.lean`, `RBM3D/Induction/PerTimeCalc.lean`; `RBM3D/Test/Axioms.lean` unchanged).  `git diff --stat main...t/T2045`:
```
 RBM3D/Induction/PerTimeCalc.lean | 1196 ++++++++++++++++++++++++++++++++++++++
 RBM3D/Induction/ScaleFacts.lean  |  700 ++++++++++++++++++++++
 2 files changed, 1896 insertions(+)
```
**b.1 Builds** (acceptance: `lake build` of each module, then the whole library)
```
Sat Oct  3 12:54:25 UTC 2026
$ lake build RBM3D.Induction.PerTimeCalc
Build completed successfully (3247 jobs).
$ lake build RBM3D.Induction.ScaleFacts
Build completed successfully (3314 jobs).
$ lake build   # whole library, root #assert_rbm_axioms included
Build completed successfully (3743 jobs).
Sat Oct  3 12:54:33 UTC 2026
```
**b.2 Registry pre-check** (ST1-COMMON item 8; scratch file `import RBM3D`, `import RBM3D.Induction.ScaleFacts`, `import RBM3D.Induction.PerTimeCalc`, `#assert_rbm_axioms`; `lake env lean`, exit 0; no unclassified premise, no registry line needed: the Prop hypotheses used are `Sizes.WO`, `Bandwidth`, `STConStInd`, already structural)
```
$ lake env lean precheck.lean   # exit code: 0
axiom audit: 1560 theorems, 549 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms ...
premises found by scanning: 29 (borrowed 2, owed 14, structural 13).
registry: 5 borrowed + 19 owed + 23 structural; 18 registered premise(s) carry nothing yet: [...]
```
**b.3 Axioms** (`collectAxioms` over every non-private declaration of the two modules; `std3` = `[propext, Classical.choice, Quot.sound]`; prefix `RBM.` omitted)
```
Gauss.Sizes.STBctl_ge  Gauss.Sizes.STBctl_mono  Gauss.Sizes.STBctl_pos
Gauss.Sizes.STBctl_xmono  Gauss.Sizes.STsize_pos  Ind.closure_scale
Ind.closure_sq_le  Ind.PerTimeCalc.stepOneBootstrap  Ind.PerTimeCalc.Unif.forbidden_region
Ind.PerTimeCalcInst.forbidden_region_sz0  Ind.PerTimeCalcInst.stepOneBootstrap_sz0  Ind.scaleFacts_ellT_mono_ratio
Ind.scaleFacts_ellT_pow_four  Ind.scaleFacts_ellT_ratio  Ind.scaleFacts_etaT_div_etaT
Ind.scaleFacts_R1  Ind.scaleFacts_R2  Ind.scaleFacts_R2_pt
Ind.ScaleFactsInst.Bctl_facts_sz0  Ind.ScaleFactsInst.closure_sz0  Ind.ScaleFactsInst.forbidden_region_Bctl_sz0
Ind.ScaleFactsInst.R1_sz0  Ind.ScaleFactsInst.R2_pt_sz0  Ind.ScaleFactsInst.R2_sz0
Ind.ScaleFactsInst.ratio_sz0  Ind.ScaleFactsNeg.scaleFacts_R1_needs_WO
declarations checked: 90; with an axiom outside the three standard ones: 0
$ grep -nE '\b(sorry|admit|native_decide)\b|^[[:space:]]*axiom ' RBM3D/Induction/ScaleFacts.lean RBM3D/Induction/PerTimeCalc.lean
grep exit: 1
```
**b.4 Target statements, ScaleFacts** (extracted by script, `variable {d : ℕ} (sz : Sizes d)` precedes each); RBM2D token diff of the signatures (`c9a24cf`, script `tokdiff.py`, parentheses omitted)
```
-- ScaleFacts.lean:193
theorem scaleFacts_R1 (𝔠 𝔡 τ : ℝ) (t : ℕ → ℝ) (h𝔡 : 0 < 𝔡)
    (hB : sz.Bandwidth 𝔠) (hWO : sz.WO 𝔡)
    (hR : ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + τ) ≤ 1 - t n) :
    ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, u ≤ t n →
      sz.Bctl n u ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (-(min (2 * 𝔠 * 𝔡) τ)) :=
-- ScaleFacts.lean:267
theorem scaleFacts_R2_pt (n : ℕ) {c s u t : ℝ} (hc : 0 < c) (hsu : s ≤ u) (hut : u ≤ t)
    (ht : t < 1) (hstep : (sz.Bctl n t) ^ c ≤ (1 - t) / (1 - s)) :
    sz.Bctl n u ≤ (sz.Bctl n s) ^ (1 - c) :=
-- ScaleFacts.lean:287
theorem scaleFacts_R2 {𝔠d : ℝ} (h𝔠d : 0 < 𝔠d) {s t : ℕ → ℝ} (hC : sz.STConStInd 𝔠d s t)
    (ht : ∀ᶠ n : ℕ in atTop, t n < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, s n ≤ u → u ≤ t n →
      sz.Bctl n u ≤ (sz.Bctl n (s n)) ^ (1 - 𝔠d) :=
-- ScaleFacts.lean:330
theorem scaleFacts_ellT_ratio {L : ℕ} {g s u t : ℝ} (hL : 1 ≤ L) (hsu : s ≤ u) (hut : u ≤ t)
    (ht : t < 1) :
    ellT L g u / ellT L g s ≤ ((1 - s) / (1 - t)) ^ ((1 : ℝ) / 2) :=
-- ScaleFacts.lean:349
theorem scaleFacts_ellT_pow_four {L : ℕ} {g E s t : ℝ} (hL : 1 ≤ L) (hE : |E| < 2)
    (hst : s ≤ t) (ht : t < 1) :
    (ellT L g t / ellT L g s) ^ 4 ≤ (etaT E s / etaT E t) ^ 2 :=
scaleFacts_R1: only in RBM2D 0 0 < < E E E E L RangeCond W c c c c d d d d d h h hE hc im n n scaleM spectralM | | κ κ κ κ τ τ | only in RBM3D * + - - . 1 1 Bctl WO ^ atTop hWO h𝔡 in size sz sz sz sz sz ℕ ℕ ℝ 𝔠 𝔠 𝔠 𝔡 𝔡 𝔡 𝔡
scaleFacts_R2_pt: only in RBM2D / 1 2 29 30 30 E E E E E L L L L L W W W W W hE hL hW s scaleM scaleM scaleM | | ¹ ⁻ ℝ ≤ ≤ | only in RBM3D - . . . 0 Bctl Bctl Bctl c c c c hc n n n n sz sz sz t
scaleFacts_ellT_ratio: only in RBM2D 0 hs0 s ≤ | only in RBM3D g g g
scaleFacts_ellT_pow_four: only in RBM2D 0 hs0 s ≤ | only in RBM3D g g g
```
**b.5 Target statements, PerTimeCalc** (`Unif.forbidden_region`, `stepOneBootstrap`; section variables `{Ω} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ} {U : ℕ → Type*}`).  `diff` of RBM2D `PerTimeCalc.lean:67-849` against the RBM3D file lines 49-831: 4 differing lines (docstring of `stepOneBootstrap`, `T2006 (b.7) rule 3` removed):
```
-- PerTimeCalc.lean:680
theorem forbidden_region (hsize : Tendsto size atTop atTop) {x : ∀ l, U l → Ω → ℝ}
    {f a b : ∀ l, U l → ℝ}
    (ha : ∀ l u, 0 < a l u) {ε : ℝ} (hε : 0 < ε)
    (hfa : ∀ᶠ l : ℕ in atTop, ∀ u, f l u ≤ (size l : ℝ) ^ (-ε) * a l u)
    (h : StochDomAt P size (fun l u ω => {ω | x l u ω ≤ b l u}.indicator (fun ω => x l u ω) ω)
      (fun l u _ => f l u)) :
    HighProbAt P size (fun l => {ω | ∀ u, x l u ω < a l u ∨ b l u < x l u ω}) :=
-- PerTimeCalc.lean:808
theorem stepOneBootstrap (hsize : Tendsto size atTop atTop)
    {M : ∀ _ : ℕ, ℝ → Ω → ℝ} {a b : ∀ _ : ℕ, ℝ → ℝ} {s t : ℕ → ℝ}
    (hcont : HighProbAt P size
      (fun l => {ω | ContinuousOn (fun u => M l u ω) (Set.Icc (s l) (t l))}))
    (ha : ∀ l, ContinuousOn (a l) (Set.Icc (s l) (t l)))
    (hab : ∀ᶠ l : ℕ in atTop, ∀ u : TimeIcc s t l, a l u ≤ b l u)
    (hforb : HighProbAt P size
      (fun l => {ω | ∀ u : TimeIcc s t l, M l u ω < a l u ∨ b l u < M l u ω}))
    (hinit : HighProbAt P size (fun l => {ω | M l (s l) ω < a l (s l)})) :
    HighProbAt P size (fun l => {ω | ∀ u : TimeIcc s t l, M l u ω < a l u}) :=
```
**b.6 Probe 4.1 statements** (`752e027:RBM3D/Probe/T2015Pins.lean`, section 4.1; `STsize_pos`, `STBctl_*` in `namespace RBM.Gauss.Sizes` with `variable {d : ℕ} (sz : Sizes d)`, `closure_*` in `RBM.Ind`), and the comparison of statement and proof text with the probe (whitespace-normalised)
```
-- ScaleFacts.lean:58
theorem STsize_pos (n : ℕ) : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) :=
-- ScaleFacts.lean:64
theorem STBctl_pos (n : ℕ) {t : ℝ} (ht : t < 1) : 0 < sz.Bctl n t :=
-- ScaleFacts.lean:74
theorem STBctl_mono (n : ℕ) {s u : ℝ} (hsu : s ≤ u) (hu : u < 1) : sz.Bctl n s ≤ sz.Bctl n u :=
-- ScaleFacts.lean:93
theorem STBctl_xmono (n : ℕ) {s v : ℝ} (hsv : s ≤ v) (hv : v < 1) :
    (1 - v) * sz.Bctl n v ≤ (1 - s) * sz.Bctl n s :=
-- ScaleFacts.lean:126
theorem STBctl_ge (n : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ((((sz.W n : ℕ) : ℝ) ^ d))⁻¹ * (sz.lam n ^ 2 + 1)⁻¹ ≤ sz.Bctl n s :=
-- ScaleFacts.lean:156
theorem closure_scale {as at_ xs xt xu c : ℝ} (hc : 0 < c) (has : 0 < as) (hat : as ≤ at_)
    (hxt : 0 < xt) (hxs : 0 < xs) (hxu : xt ≤ xu) (hcon : at_ ^ c ≤ xt / xs) :
    as * (xs / xu) ≤ as ^ (1 - c) :=
-- ScaleFacts.lean:170
theorem closure_sq_le {a c : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hc : c ≤ 1 / 4) :
    a ^ (1 - c) ≤ (a ^ (3 / 8 : ℝ)) ^ 2 :=
STsize_pos: probe line 946, file line 58 identical: True
STBctl_pos: probe line 952, file line 64 identical: True
STBctl_mono: probe line 962, file line 74 identical: True
STBctl_xmono: probe line 981, file line 93 identical: True
STBctl_ge: probe line 1014, file line 126 identical: True
closure_scale: probe line 1042, file line 156 identical: True
closure_sq_le: probe line 1056, file line 170 identical: True
```
**b.7 Compiled nonempty instances** (`sz0`, `d = 3`; every deterministic hypothesis discharged; `hsize := tendsto_sz0_size`; random observable `obs`, window `[0, 1/16]`)
```
-- PerTimeCalc.lean:894
theorem forbidden_region_sz0 :
    HighProbAt (seqP sz0) sz0.size
      (fun n => {ω | ∀ u : TimeIcc s0 t0 n, xF n u ω < 1 ∨ 2 < xF n u ω}) :=
-- PerTimeCalc.lean:916
theorem stepOneBootstrap_sz0 :
    HighProbAt (seqP sz0) sz0.size
      (fun n => {ω | ∀ u : TimeIcc s0 t0 n, (u : ℝ) * obs n ω < 1}) :=
-- ScaleFacts.lean:384
theorem R1_sz0 : ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, u ≤ tInst n →
    sz0.Bctl n u ≤ 2 * ((sz0.size n : ℕ) : ℝ) ^ (-(min (2 * (1 / 6) * (1 / 10)) (1 / 10 : ℝ))) :=
-- ScaleFacts.lean:424
theorem R2_sz0 : ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, sInst n ≤ u → u ≤ tInst n →
    sz0.Bctl n u ≤ (sz0.Bctl n (sInst n)) ^ (1 - 1 / 100 : ℝ) :=
-- ScaleFacts.lean:431
theorem R2_pt_sz0 : ∃ n : ℕ, sz0.Bctl n (1 / 32) ≤ (sz0.Bctl n 0) ^ (1 - 1 / 100 : ℝ) :=
```
Also compiled, statements in `ScaleFacts.lean` / `PerTimeCalc.lean`: `ScaleFactsInst.{ratio_sz0 (ratio facts at `L=4`, `g=1/64`, `s=1-10^{-4}`, `t=1-(4·10^4)^{-1}`), ratio_sz0_sharp (both sides `2`), ell_values, R1_sz0_lt_one, Bctl_facts_sz0 (`STBctl_pos/mono/xmono/ge`, `closure_sq_le`), closure_sz0 (`STsize_pos`, `closure_scale`), forbidden_region_Bctl_sz0 (actual scales, `ε = 1/480`)}`, `ScaleFactsNeg.scaleFacts_R1_needs_WO` (the counterexample without `(eq:WO)`), and 44 `example`s in `PerTimeCalc.lean` (`Xi ≺ Ze ≺ Ch` of `StochDomAtInst`), checked by script `covcheck.py`:
```
public declarations in PerTimeCalc.lean lines 49-833: 46; not named (whole word) in lines 835-1196: []
example blocks in file: 44
```
**b.8 Name clashes and ports**
```
env.contains on the merged root (import RBM3D): names checked: 90; clashes: 0 (merge base 3747ff7)
main tip 057edb0: 90 new public names, 71 short names, same-short-name declarations on main: 1
t0: main:RBM3D/Gauss/BlockAnderson.lean:170:def t0 : ℝ := 1 / 4
# t0: main has RBM.Gauss.BlockAndersonInst.t0 (BlockAnderson.lean:150-170); ours is RBM.Ind.PerTimeCalcInst.t0: distinct full names, no clash
$ git -C ../RBM2D diff --stat c9a24cf HEAD -- ScaleFacts PerTimeCalc Path/Scales   # RBM2D HEAD 9e0f275; ported text is c9a24cf (ticket)
 RBM2D/Induction/PerTimeCalc.lean | 970 ++-------------------------------------
 RBM2D/Induction/ScaleFacts.lean  | 170 ++-----
 RBM2D/Path/Scales.lean           | 129 +-----
 3 files changed, 89 insertions(+), 1180 deletions(-)
$ git -C ../RBM1D diff --stat 86573b9 HEAD -- Step1 ContinuityAssembly Step45 StochDomHighProb   # RBM1D HEAD de0de42; cited in the PerTimeCalc docstring, text taken from the RBM2D copy
 RBM1D/Hierarchy/Step1.lean         | 435 ++-----------------------------------
 RBM1D/Hierarchy/Step45.lean        | 346 ++---------------------------
 RBM1D/Loop/ContinuityAssembly.lean | 368 +------------------------------
 3 files changed, 54 insertions(+), 1095 deletions(-)
```
**b.9 `d = 2` tokens of the two RBM2D files** (portmap kinds `W2 L2 N2 inv2 d2`, plus `Z2`, `1/5`, `scal` = uses of `scaleM ellStar tailT ellT`, `e30` = exponent 30 / 29/30; code lines only) and the code lines of the dropped declarations
```
== Induction/ScaleFacts@c9a24cf code-line token hits by kind: {'scal': 40, 'e30': 10};
  by declaration: scaleFacts_R1: scal: 2; scaleFacts_R2_pt: scal: 6, e30: 6; scaleFacts_R2: scal: 2, e30: 1; scaleFacts_ellT_ratio: scal: 1; scaleFacts_ellT_pow_four: scal: 3; chainStepCond: scal: 7, e30: 2; scaleFacts_inv_sq_le_tailT: scal: 13; R1_instance: scal: 1; R2_instance: scal: 2, e30: 1; ratio_instance: scal: 3
== Induction/PerTimeCalc@c9a24cf code-line token hits by kind: {}
code lines 308 {'ChainStepCond': 6, 'chainStepCond': 95, 'scaleFacts_inv_sq_le_tailT': 34}
```
Accounting: `scal`/`e30` in `scaleFacts_R1`, `R2_pt`, `R2`, `ellT_ratio`, `pow_four` are replaced (`scaleM → Bctl`, `ellT L u → ellT L g u`, `30, 29/30 → c, 1-c`); the hits in `chainStepCond`, `scaleFacts_inv_sq_le_tailT`, `R1/R2/ratio_instance` belong to dropped declarations or to instances redone at `sz0`.  `W2 L2 N2 inv2 d2 Z2 1/5`: none in either file; `PerTimeCalc`: none (dimension free).

**b.10 Narrative**
- PerTimeCalc: RBM2D `PerTimeCalc.lean:67-849` (the `PerTime` and `Unif` calculus, `forbidden_region`, `stepOneBootstrap`) is copied over the merged scale-`size` vocabulary of `RBM3D/Defs/StochDomAt.lean`; the namespaces `RBM.Ind.PerTimeCalc.{PerTime,Unif}` are those of the RBM2D file, `hsize` stands where RBM2D has it, 4 docstring lines differ (b.5).  The file is dimension free.  Not copied: RBM2D's toy section, compiled negatives and axiom audit (lines 851-1434), replaced by the instances of b.7.
- ScaleFacts, the `d`-dimensional exponent per statement (`a_t := W^{-d} B_{t,0} = sz.Bctl n t`, `x = 1 - t`, `N = sz.size n = (W L)^d`):
  * R1: `a_u = (W^d (g²+x_u))⁻¹ + (N x_u)⁻¹ ≤ (g² W^d)⁻¹ + N^{-τ} ≤ W^{-2𝔡} + N^{-τ} ≤ 2 N^{-min(2𝔠𝔡, τ)}` for `u ≤ t`, from `Sizes.lam_sq_mul_pow_ge` (`(eq:WO)`), `W ≥ N^𝔠`, `x_u ≥ x_t ≥ N^{-1+τ}`.  RBM2D's `min(2c, τ)` becomes `min(2𝔠𝔡, τ)`; the conclusion is on `a_u` (RBM2D: on `M_u`), with the extra hypothesis `sz.WO 𝔡`.  `scaleFacts_R1_needs_WO` (b.7) compiles the reason: `ilambda ≡ 0`, `W = L = n+3`, `Bandwidth (1/6)`, `N^{-9/10} = 1 - t_n`, `¬ WO`, and `2 N^{-1/30} < W^{-3}B_{t_n,0}` at every `n`.
  * R2_pt, R2: RBM2D's `30`, `29/30` become `1/c`, `1 - c`, `c = 𝔠_d` (`c = 1/30` is RBM2D's `29/30`): `a_u ≤ a_s^{1-c}` from `x_u a_u ≤ x_s a_s` (`STBctl_xmono`), `a_s ≤ a_t` (`STBctl_mono`) and `closure_scale`.  `scaleFacts_R2` takes `STConStInd` and `∀ᶠ n, t n < 1`.
  * ellT_ratio, ellT_pow_four: exponents `1/2`, `4`, `2` unchanged (`4·1/2 = 2`); proof `max(a r, 1) ≤ r·max(a, 1)` for `r ≥ 1` and the cap `L`; sharp (b.7: both sides `2`).
- Residual differences from RBM2D (ST1-COMMON item 6; b.4): R1: `κ E hE hκ hc hτ` removed, `spectralM`, `scaleM` replaced as above, `RangeCond d τ t` written out, `hWO` added; R2_pt: `L W E hL hW hE` replaced by `sz n`, hypothesis and conclusion in `Bctl` with `c`, `0 < c` added; ratio facts: `g` added (merged `ellT L g`), `hs0 : 0 ≤ s` dropped.
- Dropped: `ChainStepCond`, `chainStepCond` (101 code lines), `scaleFacts_inv_sq_le_tailT` (34), and the private checks of the RBM2D file (reasons in (d)).
- From the probe (portmap: new = probe 4.1), text identical (b.6): `STsize_pos`, `STBctl_pos/mono/xmono/ge` (namespace `RBM.Gauss.Sizes`), `closure_scale`, `closure_sq_le` (`RBM.Ind`).  Helpers `scaleFacts_ellT_mono_ratio`, `scaleFacts_etaT_div_etaT` (RBM2D `Path/Scales.lean:135`, `:92`) carry the file stem.
- Instances (b.7): every statement of b.4 and b.5 and every public theorem of the copied PerTimeCalc body is applied at `sz0` with every deterministic hypothesis discharged (44 `example`s plus the named theorems).  `forbidden_region_Bctl_sz0` runs the Step 1 chain: `a = α = (W^{-3}B_{0,0})^{1/4}`, `f = α^{3/2}`, `ε = 1/480`, and `f ≤ N^{-ε} a` is discharged from `scaleFacts_R1` (`Bctl_eighth_le`).  The stochastic premises of the instances hold sample-wise (`x ≤ f` pointwise), so the instances test the shapes and the exponent bookkeeping, not a probabilistic estimate.
- No registry line: the pre-check (b.2) passes with `RBM3D/Test/Axioms.lean` unchanged.

## (c) Verified Mathlib names
`env.contains` script over the names used in the new code: Mathlib names checked with env.contains: 50; absent: 0.  Present: 
```
Real.rpow_le_rpow_of_exponent_le  Real.rpow_le_rpow_of_nonpos  Real.rpow_le_rpow_of_exponent_ge  Real.rpow_le_one_of_one_le_of_nonpos  Real.pow_rpow_inv_natCast
Real.sqrt_div  Real.sqrt_eq_rpow  Real.sqrt_sq  Real.sqrt_pos  Real.sqrt_le_sqrt
Real.le_sqrt_of_sq_le  Real.rpow_natCast  Real.rpow_mul  Real.rpow_add  Real.rpow_neg
Real.rpow_one  Real.mul_rpow  Real.rpow_pos_of_pos  Real.rpow_nonneg  Real.rpow_le_rpow
Real.one_le_rpow  inv_anti₀  div_le_div_of_nonneg_left  div_le_div_iff₀  le_div_iff₀
div_le_iff₀  one_le_div  le_self_pow₀  one_le_pow₀  inv_le_one_of_one_le₀
mul_div_mul_right  mul_le_mul_of_nonneg_left  pow_le_pow_left₀  le_add_of_nonneg_right  mul_left_cancel₀
continuousOn_const  Set.indicator_of_mem  Set.indicator_of_notMem  Set.indicator_univ  min_eq_left
min_eq_right  max_le  abs_of_pos  sub_sub_cancel  inv_inv
Filter.Tendsto.eventually_ge_atTop  Filter.Eventually.exists  intermediate_value_Icc'  MeasureTheory.measure_union_le  tendsto_natCast_atTop_atTop
```
Grouped five per line to keep the report within 300 lines; `measure_union_le` exists only as `MeasureTheory.measure_union_le`.

## (d) Open issues and paper-delta candidates
1. Not ported, although the portmap does not mark them unused: `ChainStepCond`, `chainStepCond` (consumers at `c9a24cf`: `Induction/Chain`, `Induction/MainInd`) and `scaleFacts_inv_sq_le_tailT` (consumer `Induction/Step45`; `tailT`, `ellStar`, `scaleM` have no `d ≥ 3` object).  The `d ≥ 3` paper (`1_2:1308-1312`) states the induction on `t` in two phases and fixes no grid `s_k`; a step lemma of the chain induction would be `scaleFacts_R1` + `scaleFacts_R2` at the chosen grid.  Dispatcher decision for the chain-induction ticket.
2. Probe section 4.0 (`StochDomAt.of_subset_whp`, `of_subset_compl`; not in the merged `StochDomAt.lean`) is outside this ticket (portmap: new = probe 4.1); the composition of Step 1 needs it.
3. `ScaleFacts.lean` imports `RBM3D.Induction.Defs` and `RBM3D.Induction.PerTimeCalc` (the latter only for `forbidden_region_Bctl_sz0`); `PerTimeCalc.lean` imports `RBM3D.Defs.StochDomAt` and `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`; neither imports `RBM3D` itself.  Hub, at merge: add `import RBM3D.Induction.PerTimeCalc` and `import RBM3D.Induction.ScaleFacts` after the last import of `RBM3D.lean`.
4. Paper-delta candidates.  T2045a: `scaleFacts_R1` is a statement on `W^{-d}B_{t,0}` (`1_2:1108`) with `(eq:WO)` (`1_2:363`) as hypothesis (RBM2D: on `M_t`); the ratio facts (`1_2:1121`) need no `0 ≤ s`.  T2045b: `ChainStepCond`, `chainStepCond`, `scaleFacts_inv_sq_le_tailT` have no counterpart in this paper's Lean (item 1).
5. Mathlib API: no name to add to `docs/mathlib-api.md` beyond (c).
