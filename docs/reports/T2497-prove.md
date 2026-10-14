Prover model: claude-sonnet-5-5
## (a) Math preflight — 2026-10-14 00:45 UTC (`date -u`: Wed Oct 14 00:45:47 UTC 2026)

Row a only (U1s2a, QGrid, targets 1-9). Layout (new files `Chain/QGridGen`, `Chain/QGridGen2`) and rows unchanged by this section.

### (i) Exponent table (row a; targets 6, 7, 8 carry all the constants; targets 1-5, 9 only re-state them)
| constant | value | constraint it must satisfy | slack |
|---|---|---|---|
| mollifier sup constant `C` (target 6, `QopAlgebra_mollifier_props`, `QopAlgebra:511`) | `(1+40dm)·6^(dm)`; d=3, m=3: 3638048256 | `‖ϑ_t a‖ ≤ C` for `0≤t<1` and `‖ϑ_v-ϑ_u‖ ≤ C(1-v)⁻¹Δ` (from `‖∂ϑ‖ ≤ C(1-t)⁻¹`); independent of `g=sz.lam n>0`, `L≥3` | none needed (fixed numeral; `0 ≤ C` is the only use in target 8) |
| Taylor constant `C₂` (`QGridA_mollifier_taylor2`, `QGridA:1233`) | `1000(1+dm)²`; d=3, m=3: 100000 | `‖ϑ_{u+Δ}-ϑ_u-Δ∂ϑ_u‖ ≤ C₂(1-(u+Δ))⁻²Δ²` | none needed (`0 ≤ C₂`) |
| `C = C(d,m)`, `C₂ = C₂(d,m)` quantifier position | numerals in the statement `T2497_GridDriftQNgAt` | must not be an `∃` after `(sz, z)`; they depend on `(d,m)` only | satisfied: both are closed terms of `(d,m)` |
| tensor length `k = m+1`, `m` | `1 ≤ m`, `k ≥ 2` | `SumWeightedStepErrNg_Stmt` needs `2 ≤ k` (`GridEnvelopeGen:235`) | `m=3`: `k=4`, slack 2 |
| decay exponent fed to the merged pin | `D' = D_t + (m+1)` | `(1+C·L^{dm}) ≤ (1+C)N^m` costs `N^m`; `(1+C)N^m N^{-(D_t+m+1)} = (1+C)N^{-D_t}N^{-1} ≤ N^{-D_t}/2` needs `N ≥ 2(1+C)` (eventually) | `N_0 = 2097152`; `2(1+C) = 7.28e9`; holds for `n ≥ 1` (`N_1 = 5.5e11`), eventual in `n` as stated |
| row 1 of target 8 | `8+(4k+8)(1-τ')+2D'` (`k=m+1`, `D'=D_t+m+1`) | `< C_K` | m=3, τ'=τ_K=1/2, D_t=1: 30 < 31, slack 1 |
| row 2 | `3+4τ_K+5k(1-τ')+D'` | `< C_K` | 20 < 31, slack 11 |
| row 3 | `2(1-τ')+τ_K+2k(1-τ')+D'` | `< C_K` | 10.5 < 31, slack 20.5 |
| row 4 | `1-τ'` | `< C_K` | 0.5 < 31, slack 30.5 |
| rows = rows of the merged pin | rows 1-3 of `SumWeightedStepErrNg_Stmt` at `(k, D_t) := (m+1, D_t+m+1)` | the three rows of the pin are literally rows 1-3 of target 8; row 4 is the pin's | identical expressions, no loss |
| `Δ²`-part of `qStepErrN` (band `qGridB_extra_sum_le`) | needs `k+2τ_K+(3k+2)(1-τ')+D_t < C_K` | implied by row 2: `row2 - need = 3+2τ_K+2m(1-τ') > 0` | m=3: need 13 < 31; row2 - need = 7 |
| exponent `e = k+(1-τ')(3k+2)+2τ_K-C_K` | `< -D_t` (`qGridB_eventually_le`) | `A·N^e ≤ N^{-D_t}` eventually, `A = 2^k a_Q c⁻²ᵏ` | e = -19 < -1, slack 18 |
| `E'_n = 2√(1-(Im m_n)²)` (target 8) | `Im m(E') = Im m_n` (`GridEnvelopeGen_mE_im_Ep:206`); `|E'| ≤ 2-κ_m²` (`_abs_Ep_le:217`) | need `0 < κ_m ≤ Im m_n ≤ 1` (`DecayGen_Spec`, inline `Im m ≤ 1`); band theorem at `κ := κ_m²` | slack `2-κ_m²-|E'| = (1-√(1-κ_m²))²`; κ_m = 1/2: 0.01795 (tightest, Im m = κ_m); Im m=1: 1.75 |
| `η` at E' | `etaT E'_n u = (1-u)Im m_n = Cm.eta n u` | pointwise equality for all `u` (from `DecayGen_Spec`); qErrQN reads `E` only through `etaT E` and `stepErrN` | exact equality |
| generator row bound (target 2, `HierDriftGen_UStep` (b)+(a), `HierDriftGen:666`) | `∑_b‖θ_u(a,b)‖ ≤ (1-u)⁻¹` for `0≤u<1` | (a): `∑‖uKer(u,u+Δ)-1‖ ≤ Δ(1-u-Δ)⁻¹`; (b): `∑‖uKer-1-Δθ‖ ≤ Δ²(1-u-Δ)⁻²` ⇒ `∑‖θ‖ ≤ (1-u-Δ)⁻¹+Δ(1-u-Δ)⁻²` for every `0<Δ<1-u`; let `Δ→0⁺` | exact limit `(1-u)⁻¹`, no loss; excess at u=1/10: 2.5e-2 (Δ=1e-2), 2.5e-8 (Δ=1e-8) |
| `Θ` bound from rows (target 2) | `‖Θ_{u,σ}A‖_max ≤ k(1-u)⁻¹‖A‖_max` | `k` slots, each a row-sum `≤ (1-u)⁻¹` (`QGridA:1408`) | none |
| `η ≤ 1` (target 4) | `η_u = (1-u)Im m ≤ 1` for `0≤u`, `‖m‖ ≤ 1` (`NQGood1Gen_eta_le_one:441`) | inline `‖Cm.m n‖ ≤ 1`; `‖STmsigg‖ = ‖m‖ ≤ 1` for `|avgErr| ≤ η⁻¹+1` | equality `‖m‖ = 1` not used |
| row sums of `Cm.S n` (target 4, counting) | `≤ 1` | `∑_{a,b}‖S_ab‖ ≤ L^d` replaces band `= 1` | one-sided only needed |
| stopped Duhamel (target 7) | `Step2Gen_USemigroup` | replaces `|E n|<2`; grid times `0 ≤ u_i < 1` for `i ≤ K n` | grid u_i ≤ t_n < 1 |

No external hypothesis in row a: every class (`StepDecompGen_LoopForm/WalkForm`, `HierDriftGen_*`, `Step2Gen_USemigroup`, `DecayGen_Spec`) is discharged at the band carrier below (`bandStep2Mat sz0 E0`). The limit data are the explicit computations in (ii): `N_n → ∞` (`N_n=(128(n+1)⁶)³`), `RangeCond(1/2, t≡1/2)` iff `N_n ≥ 4`, `K_n = N_n^{31} ≥ N_n^{C_K}`.

### (ii) One nondegenerate instance (all hypotheses of targets 6, 7, 8 at once)
Data. Targets 6, 7: `d=3`, `sz0` (L_n=4(n+1), W_n=(2(n+1))⁵, lam_0=1/64), n=0, carrier `bandStep2Mat sz0 (E≡0)` (`m = mE 0 = i`, Im m = 1, ‖m‖ = 1 by `norm_mE`), `s≡1/10, t≡1/2, K≡4` (Δ=1/10), `m=3` (k=4), σ=(+,-,+,-), j=0 (target 6), stopping `τ≡3`, j=4=K (target 7, three genuine Duhamel steps), Bk = envelope of `𝒦` (exists, `GridDriftN_exists_envelope`). Target 8: same carrier, `κ_m=1/2` (`DecayGen_bandSpec` at κ=1), `E'≡0`, `s≡0, t≡1/2, K_n=N_n^{31}`, `τ'=τ_K=1/2`, `D_t=1`, `C_K=31`, `m=3`, `C, C₂` as in (i). Non-vacuity of the eventual statement: the script bounds the left side at n = 0, 1, 2, 3, 5 (uniform worst case over the grid: η⁻¹=2, β=2, weight 3⁴, ≤ K terms; exact binomial `uStepC`).

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2497/rowa_inst.py`
```
rows of target 8 (need < C_K=31): 30 20 21/2 1/2
slacks: 1 11 41/2 61/2
delta^2-part exponent e = -19  need e < -D_t = -1  slack 18
delta^2-part row (k+2tK+(3k+2)th+Dt) = 13 < row2 = 20  diff row2-need = 7 = 3+2tK+2m th = 7
mollifier C = (1+40dm)6^(dm) = 3638048256  C2 = 1000(1+dm)^2 = 100000
sz0: L0,W0,N0 = 4 32 2097152  lam0 = 1/64; N1 = 549755813888  N2 = 812479653347328
RangeCond(1/2, t=1/2): N^(-1/2) <= 1/2  iff N>=4: N0 = 2097152 >= 4: True
E' table, kappa_m=1/2 (bound 2-kappa_m^2 = 7/4):
  Im m = 1  E' = 0.0  Im m(E') = 1.0  slack to 2-k^2 = 1.75
  Im m = 9/10  E' = 0.8717797887  Im m(E') = 0.9  slack to 2-k^2 = 0.87822021
  Im m = 3/4  E' = 1.322875656  Im m(E') = 0.75  slack to 2-k^2 = 0.42712434
  Im m = 1/2  E' = 1.732050808  Im m(E') = 0.5  slack to 2-k^2 = 0.017949192
  exact slack at y=kappa: (1-sqrt(1-k^2))^2 = 0.017949192
generator row bound limit at u = 1/10  target (1-u)^-1 = 10/9
  Delta=1e-1: bound = 1.40625  (excess 0.295139)
  Delta=1e-2: bound = 1.1362201742204  (excess 0.0251091)
  Delta=1e-4: bound = 1.1113580658497  (excess 0.000246955)
  Delta=1e-8: bound = 1.1111111358025  (excess 2.46914e-8)
target 8 at n=0: N=2.09715e+6  log10(sum bound)=-47.8609  log10(N^-1)=-6.32163  holds=True
target 8 at n=1: N=5.49756e+11  log10(sum bound)=-107.465  log10(N^-1)=-11.7402  holds=True
target 8 at n=2: N=8.1248e+14  log10(sum bound)=-142.331  log10(N^-1)=-14.9098  holds=True
target 8 at n=3: N=1.44115e+17  log10(sum bound)=-167.069  log10(N^-1)=-17.1587  holds=True
target 8 at n=5: N=2.12987e+20  log10(sum bound)=-201.935  log10(N^-1)=-20.3284  holds=True
grid: Delta = 1/10  u_i = ['1/10', '1/5', '3/10', '2/5', '1/2']  all in [0,1): True
target 6: j=0<K: True  1<=m: True  0<lam_0: True  u_0+Delta=u_1<1: True
target 7: j=4<=K: True  min(j,tau)= 3  (3 genuine Duhamel steps)
generator row bound k(1-u_0)^-1 = 40/9  uStepC(k,Delta,u_1) = 0.16430664
```

Reading of the output: the four rows hold with slack 1 / 11 / 20.5 / 30.5; the generator row-bound excess tends to 0 with Δ; the E' table shows `Im m(E') = Im m` and the bound at the tightest point `Im m = κ_m`; the target-8 left side is below `N⁻¹` by 41 (n=0) to 181 (n=5) orders of magnitude at `K = N^{31}` (the eventual statement is already nonvacuous at n = 0; the Lean instance needs no explicit n).

### Verdicts
- Targets 1, 5, 9: PASS (vocabulary, `QGridA_condExp_aTrueQN`, instances; no new exponent; instances of 6-8 at the data above).
- Target 2: PASS. The generator row bound is derivable from `HierDriftGen_UStep` (a)+(b) at `Δ→0` as in the table (watch item of the ticket closed; no narrow gate).
- Targets 3, 4: PASS (integrability from `norm_loopFine_crudeNg` with Hermitian `Hpath = Ψ n + pathH`; envelope uses inline `‖m‖ ≤ 1` and `∑_b‖S_ab‖ ≤ 1`).
- Targets 6, 7: PASS (hypotheses of both hold together at the instance; the mollifier constants are numerals; `0 < sz.lam n` is the only size-level premise).
- Target 8: PASS (four rows hold with slack ≥ 1; E' route feasible: `|E'| ≤ 2-κ_m²`, `etaT E' = Cm.eta`; the rows coincide with those of the merged `SumWeightedStepErrNg_Stmt` at `(k, D_t) = (m+1, D_t+m+1)`).
- Layout and rows: unchanged by this section.

Overall verdict: PASS.

## (b) Script output (row a, targets 1-9; worktree RBM3D-wt/T2497, branch t/T2497; written Wed Oct 14 01:05:18 UTC 2026)

No (a′) section: no correction to (a) was needed.

### Commits, line counts (stop rule: wc -l at each section commit), diff
```
$ git log --format="%h %s" main..t/T2497
0a3b19f0 T2497a: stem-prefix the three band bridges
999fc1c4 T2497a: Chain/QGridGen2 (target 8 and instance), RBM3D.lean imports
f6011a93 T2497a: Chain/QGridGen (targets 1-7 and instances)
$ wc -l RBM3D/Chain/QGridGen.lean RBM3D/Chain/QGridGen2.lean
     970 RBM3D/Chain/QGridGen.lean
     154 RBM3D/Chain/QGridGen2.lean
    1124 total
$ git diff --stat main...t/T2497
 RBM3D.lean                 |   2 +
 RBM3D/Chain/QGridGen.lean  | 970 +++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Chain/QGridGen2.lean | 154 +++++++
 3 files changed, 1126 insertions(+)
$ git diff --stat main...t/T2497 -- <the 15 band files of the ticket, Chain/{Step34Gen,HierDriftGen,GridEnvelopeGen,ZeroModeGen,NQGood1Gen,KDecayGen}, BA>
(empty output above = band files untouched)
$ grep -rln QGridGen RBM3D RBM3D.lean   # importers of the new modules
RBM3D/Chain/QGridGen.lean
RBM3D/Chain/QGridGen2.lean
RBM3D.lean
```

### Builds (run after the last commit)
```
$ lake build RBM3D.Chain.QGridGen RBM3D.Chain.QGridGen2 2>&1 | tail -2
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3881 jobs).
$ lake build 2>&1 | tail -2    # whole library with #assert_rbm_axioms
non-vacuity certificates: 0 of 121 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4374 jobs).
```

### #print axioms (scratch file: `import RBM3D.Chain.QGridGen2`; 16 public vocabulary/theorem/bridge declarations and 3 instances)
```
$ lake env lean <scratch>/axioms.lean | (one declaration per line) | grep -c "[propext, Classical.choice, Quot.sound]$"   # exactly the standard three
19
$ grep -c "#print axioms" <scratch>/axioms.lean
19
$ lake env lean <scratch>/axioms.lean | grep -c "sorryAx"
0
```

### Target statements, extracted by script (`python3 extract.py <file> <names>`: declaration text up to `:=`)
```lean
-- RBM3D/Chain/QGridGen.lean. Target 1 (definitions; headers only, bodies are checked equal to the T2497_* pins below):
def aTrueQNg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
def dGridQNg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
def aFrozQNg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
def martIncQNg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
def rGridQNg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
def lkEnvNg {d : ℕ} {sz : Sizes d} (Cf : FlowFM sz) (n k : ℕ) (u Bk : ℝ) : ℝ :=
def driftEnvNg {d : ℕ} {sz : Sizes d} (Cf : FlowFM sz) (n k : ℕ) (u Bk : ℝ) : ℝ :=
def qErrQNg {d : ℕ} {sz : Sizes d} (Cf : FlowFM sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n m : ℕ) (C C₂ Bk : ℝ
-- target 5
theorem QGridGen_condExp_aTrueQNg (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ)
    (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (hKK : HierDriftGen_KLink Cm n)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0) (hj : j < K n) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
    (a : Fin (m + 1) → Zd d (sz.L n)) :
    ∀ᵐ ω ∂(Cm.Pp), MeasureTheory.condExp (filt sz j) Cm.Pp
        (fun ω' => aTrueQNg Cm s t K n ϑ σ (j + 1) ω' a) ω =
      STQop (d := d) ϑ (gridTime s t K n (j + 1))
        (fun b => MeasureTheory.condExp (filt sz j) Cm.Pp (fun ω' => AvecNg Cm s t K n (j + 1) σ ω' b) ω) a := by
-- target 6, general mollifier (first 4 lines; extra hypotheses: {C c C₂} 0 ≤ C, 0 ≤ c, ϑ, STMollifierProps, hdiff, QGridA_Taylor2 C₂ ϑ)
theorem gridDriftQNg_of (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {m : ℕ} (σ : Fin (m + 1) → Bool) (Bk : ℝ)
    (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ)
    (hExp : HierDriftGen_Expand Cm s t K n) (hKL : HierDriftGen_KLoop Cm n) (hKT : HierDriftGen_KTwo Cm n)
    (hU : HierDriftGen_UStep Cm.toFlowFM n) (hS : ∀ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
-- target 6, merged mollifier
theorem gridDriftQNg (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {m : ℕ} (σ : Fin (m + 1) → Bool) (Bk : ℝ)
    (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ)
    (hExp : HierDriftGen_Expand Cm s t K n) (hKL : HierDriftGen_KLoop Cm n) (hKT : HierDriftGen_KTwo Cm n)
    (hU : HierDriftGen_UStep Cm.toFlowFM n) (hS : ∀ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hKK : HierDriftGen_KLink Cm n) (hm1 : ‖Cm.m n‖ ≤ 1) (hlam : 0 < sz.lam n)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0) (hj : j < K n) (hm : 1 ≤ m) (hBk : 0 ≤ Bk)
    (hB : ∀ w ∈ Set.Icc (0 : ℝ) (gridTime s t K n (j + 1)), ∀ J : LoopIdx (Zd d (sz.L n)),
      J.WF → 2 ≤ J.length → J.length ≤ m + 1 → ‖Cm.KI n w J‖ ≤ Bk) :
    ∀ᵐ ω ∂(Cm.Pp), ∀ a : Fin (m + 1) → Zd d (sz.L n),
      ‖MeasureTheory.condExp (filt sz j) Cm.Pp
            (fun ω' => aTrueQNg Cm s t K n (QopAlgebra_mollifier d (sz.L n) m (sz.lam n)) σ (j + 1) ω' a) ω -
          Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n j) (gridTime s t K n (j + 1))
            (aTrueQNg Cm s t K n (QopAlgebra_mollifier d (sz.L n) m (sz.lam n)) σ j ω) a -
          (gridStep s t K n : ℂ) *
            dGridQNg Cm s t K n (QopAlgebra_mollifier d (sz.L n) m (sz.lam n)) σ j ω a‖ ≤
        qErrQNg Cm.toFlowFM s t K n m ((1 + 40 * ((d * m : ℕ) : ℝ)) * 6 ^ (d * m))
          (1000 * (1 + ((d * m : ℕ) : ℝ)) ^ 2) Bk j :=
-- target 7
theorem stoppedDuhamelQNg (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
    (τ : PathΩ sz → ℕ) (j : ℕ) (ω : PathΩ sz) (hS : Step2Gen_USemigroup Cm.toFlowFM n)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0) (hj : j ≤ K n) :
    aFrozQNg Cm s t K n ϑ σ τ j ω =
      Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n 0) (gridTime s t K n j) (aTrueQNg Cm s t K n ϑ σ 0 ω) +
        ∑ i ∈ Finset.range (min j (τ ω)),
          Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n (i + 1)) (gridTime s t K n j)
            ((gridStep s t K n : ℂ) • dGridQNg Cm s t K n ϑ σ i ω + martIncQNg Cm s t K n ϑ σ i ω +
              rGridQNg Cm s t K n ϑ σ i ω) := by
-- RBM3D/Chain/QGridGen2.lean, target 8
theorem sum_weighted_qErrQNg_le :
    ∀ (d : ℕ) (sz : Sizes d) (Cm : Step2Mat sz) {κm τ' τK C_K D_t C C₂ : ℝ} {s t : ℕ → ℝ} {K : ℕ → ℕ} (m : ℕ),
    0 ≤ C → 0 ≤ C₂ → DecayGen_Spec Cm.toFlowFM κm → (∀ n, (Cm.m n).im ≤ 1) → 0 < τ' → τ' ≤ 1 → 0 < τK →
    0 ≤ D_t → 1 ≤ m → sz.SizeTendsto → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → (∀ n, K n ≠ 0) →
    sz.RangeCond τ' t →
    8 + (4 * ((m : ℝ) + 1) + 8) * (1 - τ') + 2 * (D_t + ((m : ℝ) + 1)) < C_K →
    3 + 4 * τK + 5 * ((m : ℝ) + 1) * (1 - τ') + (D_t + ((m : ℝ) + 1)) < C_K →
    2 * (1 - τ') + τK + 2 * ((m : ℝ) + 1) * (1 - τ') + (D_t + ((m : ℝ) + 1)) < C_K → 1 - τ' < C_K →
    (∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) →
    ∀ᶠ n : ℕ in atTop, ∀ p ≤ K n,
      ∑ j ∈ Finset.range p, (1 + (1 - gridTime s t K n p)⁻¹) ^ (m + 1) *
          qErrQNg Cm.toFlowFM s t K n m C C₂
            (((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (gridTime s t K n (j + 1)))⁻¹ ^ (m + 1)) j ≤
        ((sz.size n : ℕ) : ℝ) ^ (-D_t) := by
```

### Pin check: scratch file = T2497_* defs of the check (lines 175-293) + examples; compile result
```
$ lake env lean <scratch>/pins.lean 2>&1 | grep -c "error:"
0
$ grep -E "^example" <scratch>/pins.lean | cut -c1-60 | paste -sd";" -
example : @aTrueQNg = @T2497_aTrueQNg := rfl;example : @dGridQNg = @T2497_dGridQNg := rfl;example : @aFrozQNg = @T2497_aFrozQNg := rfl;example : @martIncQNg = @T2497_martIncQNg := rfl;example : @rGridQNg = @T2497_rGridQNg := rfl;example : @lkEnvNg = @T2497_lkEnvNg := rfl;example : @driftEnvNg = @T2497_driftEnvNg := rfl;example : @qErrQNg = @T2497_qErrQNg := rfl;example : T2497_SumWeightedQErrQNg := sum_weighted_qErrQNg_l;example : ∀ {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (E lam;example : ∀ {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t :
```

### Compiled nonempty instances (same files; data d = 3, sz0, E0 ≡ 0; every deterministic hypothesis discharged, no hypothesis left)
```lean
-- QGridGen.lean, target 6 (first 3 lines; the conclusion continues with the pinned head at the merged constants)
theorem QGridGen_gridDriftQNg_instance :
    STAlternating QGridGen_sigma4 ∧
    ∃ Bk : ℝ, 0 ≤ Bk ∧ ∀ᵐ ω ∂(Cm0.Pp), ∀ a : Fin (3 + 1) → Zd 3 (sz0.L 0),
-- QGridGen.lean, target 7 (first 2 lines): τ ≡ 3, j = 4 = K 0, three genuine Duhamel steps, every path ω
theorem QGridGen_stoppedDuhamelQNg_instance (ω : PathΩ sz0) :
    STAlternating QGridGen_sigma4 ∧
-- QGridGen.lean, target 5 and the Taylor input (examples, line numbers)
958:example (a : Fin (3 + 1) → Zd 3 (sz0.L 0)) :=
963:example : QGridA_Taylor2 (d := 3) (1000 * (1 + ((3 * 3 : ℕ) : ℝ)) ^ 2) moll :=
-- QGridGen2.lean, target 8 (full)
theorem QGridGen2_sum_weighted_qErrQNg_instance :
    ∀ᶠ n : ℕ in atTop, ∀ p ≤ QGridGen2_Kc31 n,
      ∑ j ∈ Finset.range p,
          (1 + (1 - gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) QGridGen2_Kc31 n p)⁻¹) ^ (3 + 1) *
          qErrQNg Cm0.toFlowFM (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) QGridGen2_Kc31 n 3
            ((1 + 40 * ((3 * 3 : ℕ) : ℝ)) * 6 ^ (3 * 3)) (1000 * (1 + ((3 * 3 : ℕ) : ℝ)) ^ 2)
            (((sz0.size n : ℕ) : ℝ) ^ (1 / 2 : ℝ) *
              (Cm0.eta n (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) QGridGen2_Kc31 n
                (j + 1)))⁻¹ ^ (3 + 1)) j ≤
        ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) :=
```

### Greps (hypothesis rules of the ticket)
```
$ grep -cE "<X1-C4 regex of the ticket: (def|abbrev|structure) of a merged name>" QGridGen*.lean
RBM3D/Chain/QGridGen.lean:0 RBM3D/Chain/QGridGen2.lean:0
$ grep -cE "∀ \(sz : Sizes d\)|STGridRepNgL|sorry|admit|native_decide|^axiom|gK" QGridGen*.lean
RBM3D/Chain/QGridGen.lean:0 RBM3D/Chain/QGridGen2.lean:0
$ grep -nE "sz\.withLam" QGridGen*.lean
RBM3D/Chain/QGridGen.lean:707:    exact (hW.1 n).add (pathH_isHermitian (sz.withLam lam') s t K n j ω)
$ grep -cE "<C1/X1-C1 regex of the ticket>" QGridGen*.lean   # hit lines per file
RBM3D/Chain/QGridGen.lean:36 RBM3D/Chain/QGridGen2.lean:7
$ same regex, hits not containing KLloopOf (the pin vocabulary; its name contains the substring Lloop)
RBM3D/Chain/QGridGen.lean:97:/-- **`lkEnvNg`** (band `lkEnvN`, `QGridA:1319`): `etaT E u` read as `Cf.eta n u` (as `step
RBM3D/Chain/QGridGen.lean:611:  have : IsProbabilityMeasure Cm.Pp := by rw [hW.2.1]; exact isProbabilityMeasure_pathP _
RBM3D/Chain/QGridGen.lean:632:  have : IsProbabilityMeasure Cm.Pp := by rw [hW.2.1]; exact isProbabilityMeasure_pathP _
RBM3D/Chain/QGridGen.lean:707:    exact (hW.1 n).add (pathH_isHermitian (sz.withLam lam') s t K n j ω)
RBM3D/Chain/QGridGen.lean:856:        RBM.ThetaN d (sz.L n) (sz.lam n) (fun i => mSigma (E n) (σ' i)) u A :=
RBM3D/Chain/QGridGen.lean:904:private theorem hm0 : ‖Cm0.m 0‖ ≤ 1 := (norm_mE (E := E0 0) (by norm_num)).le
RBM3D/Chain/QGridGen2.lean:16:and the inline `∀ n, (Cm.m n).im ≤ 1` in place of `|E n| ≤ 2 - κ`.
RBM3D/Chain/QGridGen2.lean:19:`|E'_n| ≤ 2 - κ_m²` (`GridEnvelopeGen_mE_im_Ep`, `GridEnvelopeGen_abs_Ep_le`); `qErrQNg` r
RBM3D/Chain/QGridGen2.lean:70:  have hE'2 : ∀ n, |E' n| ≤ 2 - κm ^ 2 := fun n =>
RBM3D/Chain/QGridGen2.lean:72:  have hmE : ∀ n, (mE (E' n)).im = (Cm.m n).im := fun n =>
RBM3D/Chain/QGridGen2.lean:74:  have hetaE : ∀ n u, etaT (E' n) u = Cm.eta n u := fun n u => by
RBM3D/Chain/QGridGen2.lean:75:    rw [hspec.2.2 n u]; unfold etaT; rw [hmE n]
RBM3D/Chain/QGridGen2.lean:106:  change (mE 0).im ≤ 1
$ name clash: grep -rnw of the 22 new public names (8 vocabulary, 5 targets, 3 bridges, QGridGen_sigma4, QGridGen_sigma4_alternating, 3 instances, QGridGen2_Kc31) in RBM3D/ and ../T2497b/RBM3D, outside the two files
total hits outside: 0
```

### Narrative (row a)
- Layout as ticketed: two new files, no band file edited (empty diff above), `RBM3D.lean` +2 import lines after the last `import` (`Step5IIIWalk2`); the hub unions them with row b's lines. `QGridGen` 970 lines and `QGridGen2` 154 lines (1,124 together) against the forecast ≈ 1,150-1,170 for the row (`QGridGen` hi 1,500; QB part ≈ 90).
- Target 2 (private): `QGridGen_row_thetaKer_le` takes `HierDriftGen_UStep` (a) and (b) at `u, u+Δ`, divides by `Δ`, and lets `Δ → 0⁺` (`ge_of_tendsto` along `𝓝[>] 0`); the result gives `QGridGen_norm_ThetaN_le` (`‖Θ A‖ ≤ k (1-u)⁻¹ M`). One step of `𝒰` is the merged `HierDriftGen_UN_step_le`.
- Target 3: `QGridGen_qstep_algebra` is the band text of `QGridA_qstep_algebra` with `Ugen/ThetaN` replaced by `Step2Gen_UN/ThetaN`, the row bounds read from `HierDriftGen_UStep`, linearity from `QopAlgebra_UN_subg/_ThetaN_subg`. Integrability uses the merged `HierDriftGen_integrable_LIM`; `norm_loopFine_crudeNg` is not used (0 occurrences), the sup bound is `QGridGen_norm_LIM_le` (the proof of `HierDriftGen_norm_LIM_le` at any Hermitian `H`).
- Target 4 (private): `QGridGen_norm_drift_le` at `driftEnvNg`; `η ≤ 1` from `NQGood1Gen_eta_le_one` with the inline `‖Cm.m n‖ ≤ 1`; `‖STmsigg‖ ≤ 1`; the row sums of `Cm.S n` are used as `≤ 1` (`norm_primBilS_le` of T5s2).
- Targets 5-7: `QGridGen_condExp_aTrueQNg`; `gridDriftQNg_of` (any `ϑ`) and `gridDriftQNg` (merged mollifier at `sz.lam n`, `C = (1+40dm)6^{dm}`, `C₂ = 1000(1+dm)²`) from `gridDriftNg_at`'s per-index classes and the algebra; `stoppedDuhamelQNg` from `Step2Gen_UN_duhamel_telescope`, `Step2Gen_UN_comp`, `Step2Gen_UNHom` under `Step2Gen_USemigroup`. Hypotheses of 6 follow the check's shape example (pin check above compiles `T2497_GridDriftQNgAt`, `T2497_StoppedDuhamelQNg`).
- Target 8 (E′ route, `QGridGen2:67-84`): the band theorem at `E'_n = 2√(1-(Im m_n)²)`, `κ = κ_m²`; `Im m(E'_n) = Im m_n`, `|E'_n| ≤ 2-κ_m²` (`GridEnvelopeGen_mE_im_Ep`, `_abs_Ep_le`); `qErrQNg` reads the carrier only through `eta` (`QGridGen2_qErrQNg_eta`, `GridEnvelopeGen_stepErrNg_eta`). The substitution succeeded; the four rows are the pin's.
- `open private … from RBM3D.Induction.QGridA` (header of `QGridGen`): `QGridA_row_mul, _Psum_add, _Psum_mul, _norm_Psum_le, _norm_six_le, _time_facts, _loopOf_wf, _loopOf_length, _norm_ite_le, _length_cutGlue, _wf_cutGlue, _vartheta_sup, _vartheta_lip, _gridTime_nonneg, _gridTime_lt_one`. No `private` deleted; no band file touched.
- Family table as used (all per-index, none flow-guarded here): targets 3, 5: `LoopForm`, `WalkForm`, `KLink`; target 6: those + `Expand`, `KLoop`, `KTwo`, `UStep`, row sums `≤ 1`, `‖m‖ ≤ 1` inline, `0 < sz.lam n`; target 7: `Step2Gen_USemigroup` (owed at BA by U1-BA, ticket row 10); target 8: `DecayGen_Spec`, `∀ n, Im m ≤ 1` (rows 12). UBA-C1: R1 never enters; `gK` 0 hits; `sz.withLam` once, inside a proof (`QGridGen:707`, Hermitian `Hpath`). Registry lines: none for row a (row b owns `Test/Axioms.lean`).
- Instances (`QGridGenCheck`, `QGridGen2Check`) discharge every deterministic hypothesis at `sz0` with the band discharges of `HierDriftGen`; no hypothesis is left. Times (`date -u`): (a) at 00:45:47; commits followed `date -u` outputs 00:57:17, 00:58:37, 01:04:54.

## (c) Verified Mathlib names (`Lean.Environment.contains` script, all `true`)
`ge_of_tendsto`, `Ioo_mem_nhdsGT`, `nhdsWithin_le_nhds`, `Complex.norm_conj`, `norm_add₃_le`, `one_le_pow₀`, `pow_le_one₀`, `one_le_inv₀`, `inv_le_one_of_one_le₀`, `pow_le_pow_right₀`, `MeasureTheory.integrable_finsetSum'`, `MeasureTheory.condExp_sub`, `condExp_smul`, `condExp_finsetSum`, `le_of_eq_of_le`, `le_of_mul_le_mul_left`, `Nat.card_Icc`, `one_add_mul_le_pow`, `Real.rpow_natCast`, `norm_image_sub_le_of_norm_deriv_le_segment'`. Names verified absent: none looked for.

## (d) Open issues and paper-delta candidates
- `T2497a` (hypothesis form, targets 3-7): carrier statements take the per-index classes (`LoopForm`, `WalkForm`, `Expand`, `KLoop`, `KTwo`, `UStep`, `KLink`, `Step2Gen_USemigroup`) in place of the paper's `|E| < 2`, `M = mI`; `‖m‖ ≤ 1` inline in place of `‖m‖ = 1`; row sums of `S` `≤ 1` in place of `= 1`. Conclusions are the band's.
- `T2497b` (target 8): `DecayGen_Spec` and `∀ n, Im m ≤ 1` in place of `|E n| ≤ 2 - κ`; constants `C, C₂ ≥ 0` arbitrary as in the band; decay exponent `D_t + (m+1)` as in the band.
- Open: `Step2Gen_USemigroup` and the class discharges at BA are owed by U1-BA / U3-BA (not read here). Extra public names beyond the targets: the three `QGridGen_band*` bridges, `QGridGen_sigma4(_alternating)`, `QGridGen2_Kc31`. `RBM3D.lean` is shared with row b (union at merge). No `Test/Axioms.lean` change.
