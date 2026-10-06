Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 09:26:45 UTC 2026

### (i) Exponent table

| # | quantity | value | constraint it must satisfy | slack |
|---|---|---|---|---|
| 1 | Θ̃ zero-mode coefficient α (2.3) | ξζ/(L^d (1−T)(1−ξ)), T = ξ(1−ζ) | left inverse: J-coefficient of (1−ξS̃)(Θ_T+αJ) is −ξζ/(L^d(1−T)) + α(1−T) − αξζ = 0, using SB·J = J·SB = J, J² = L^d J, 1−T−ξζ = 1−ξ | needs ‖ξ‖<1, ζ∈[0,1] (so T≠1, ξ≠1); checked numerically (B) |
| 2 | spectral parameters ξ = xiQ z σ | m² (σ=true), \|m\|² (σ=false), m = msc z | ‖ξ‖ < 1 for 0 < Im z (norm_msc_lt_one) | at the instance \|ξ\| = 0.6006 (both σ) |
| 3 | Prop8ZeroMode time t' | t' = (1−ζ)·lemT z, lemT z = \|msc z\|² | 0 ≤ t' < 1 (lemT_pos, lemT_lt_one, 0 ≤ 1−ζ ≤ 1) | t' ≤ lemT z < 1 for every ζ ∈ [0,1]; ζ = 0 is the merged thetaDiff case |
| 4 | Prop8ZeroMode constants | Λ = 𝔡⁻¹, κ' = √(κ(4−κ))/2, c = 1/2; C₈ = C₈(d,𝔡,κ) | 0 < lam ≤ Λ (hypothesis 0 < lam ≤ 𝔡⁻¹); κ' ≤ Im mE(lemE z) (as merged thetaDiff); κ ≤ 2 else the bulk is empty (merged proof takes C = 1) | C₈ independent of L, lam, z, ζ, σ |
| 5 | target 2.4 bound | ‖Θ̃(u,v) − Θ̃(0,0)‖ ≤ 2C₈·lam⁻² | (lam² + \|1−t'\|)⁻¹ ≤ lam⁻², (\|a\|+1)^{−(d−2)} ≤ 1, αJ cancels, Θ_T(u,v) = Θ_T(0,v−u) (Theta_apply_add_right) | no log L; numeric: osc·lam² ≤ 1.75 at lam=1, 0.62 at lam=1/2 (A) |
| 6 | target 2.5 constant | C₂.₅ = 4C₈ from 2.4 (or 2C₈ by translation) × \(\|ξ\| ≤ 1\), divided by W^d | \|profP·Tilde a b − profP·Tilde a b'\| = \|ξ\| \|Θ̃ a b − Θ̃ a b'\| / W^d | constant depends on (d,𝔡,κ) only |
| 7 | ouTauMax 𝔠 𝔡 | min(𝔠/12, 𝔠𝔡/12, 1/100) (1/720 at 𝔠=1/6, 𝔡=1/10) | τU ≤ ouTauMax ⇒ 12τU ≤ 𝔠, 12τU ≤ 𝔠𝔡, τU < 𝔠𝔡, 3τU/2 < 2𝔠𝔡/3 | 3τU/2 ≤ 𝔠𝔡/8; margin 2𝔠𝔡/3 − 𝔠𝔡/8 = 13𝔠𝔡/24 (0.009028 at the instance); τU < 𝔠𝔡 margin 11𝔠𝔡/12 |
| 8 | LL scale η_LL = N^{−1+2τU} | exponent −1 + 2τU ≤ −1 + 𝔠/6 | ouEtaLL is token-equal to the scale of UNOUDiag (Pins.lean:654) | 2τU ≤ 𝔠/6 |
| 9 | QUE scale η_Q = W^{−𝔡/3} lam W^{d/2}/N | ≥ N^{−1+2𝔠𝔡/3} | (eq:WO) W^{−d/2+𝔡} ≤ lam gives η_Q N ≥ W^{2𝔡/3}; Bandwidth W ≥ N^𝔠; η_Q ≤ 1 | exponent 2𝔠𝔡/3 vs 3τU/2 ≤ 𝔠𝔡/8 (row 7); numerics at n=0,1,10,1000 (script sz0.py below) |
| 10 | ouVar identity (2.1) | ζ = 1 − e^{−t}; diag: e^{−t}S_ii + ζ/N; off-diag: e^{−t}S_ij/2 + ζ/(2N) | gvarF = S (diag) or S/2 (off-diag), gueVar = 1/N or 1/(2N), t ≥ 0 so (1−e^{−t}).toNNReal = ζ | exact identity (B) |
| 11 | row sums (2.1) | ∑_j S̃_ij = (1−ζ)·1 + ζ·N/N = 1 | IBP_sum_svarF_row needs 3 ≤ L; card Idx = (WL)^d | exact (B), min = max = 1 |
| 12 | Markov step (ouDiag_of_ouLL) | integer p ≥ (1+ε+D)/(2ε) | N·N^{δ}·N^{−2pε} ≤ N^{−D} with δ = ε | 2pε − (1+ε+D) ≥ 0, e.g. 0.010 (ε=0.01, D=10, p=551) |
| 13 | time window of the pins | 0 ≤ t ≤ ouTStar = N^{−1+τU}; ζ(t) = 1−e^{−t} ∈ [0,1) | 2.4 needs only ζ ∈ [0,1] | t* = 4.8e-7 at n=0 of sz0 |

Proof-side facts for the Markov step (mathematics): η_LL > 0 and H Hermitian give ‖Gres‖ ≤ η_LL⁻¹, so ‖G_xx‖^{2p} is bounded (the Bochner integral in UNOULL is the true expectation); the quantifier swap "per-sequence pin ⇒ ∀ᶠ n uniform in (t,E)" needs a violator pair (t,E) with 0 ≤ t ≤ ouTStar, |E| ≤ 2−κ at each n, so it requires κ ≤ 2; for κ > 2 the E-set is empty and UNOUDiag is vacuous.

### (ii) One concrete nondegenerate instance

Data: d = 3, L = 4, W = 2, lam = 1/2 (0 < lam ≤ 𝔡⁻¹ = 10), 𝔡 = κ = 1/10, z = 1/2 + i/2 (0 < Im z ≤ 1, |Re z| = 0.5 ≤ 2−κ = 1.9), ζ = 1/2, u = 0, v = (1,0,0); L^d = 64, N = (WL)^d = 512; 2.3 at ξ = 1/2, ζ = 1/100; sum_Stilde_row at ζ = ouZeta 1 = 1 − e^{−1}; pins at sz0 = SizesInst.sz0 (L = 4(n+1), W = (2(n+1))^5, lam = (2(n+1))^{−6}), 𝔠 = 1/6, 𝔡 = 1/10, τU = 1/1000 ≤ ouTauMax = 1/720.
Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2276/pre.py` (numpy 2.0.2; FFT on Z_L^3 with Ŝ(p) = (1 + 2g² Σcos p_i)/(1 + 6g²), Θ_T(0,a) = ifftn(1/(1−TŜ)); direct 64×64 and 512×512 matrices for B).
Output (verbatim):
```
== A. d=3 oscillation of Theta~ (alpha J cancels): max_a |Theta_T(0,a)-Theta_T(0,0)|, T=xi*(1-zeta); worst over z grid, sigma, zeta
g=1.00  max osc*g^2 at L=4,8,16,32,64: 1.5165  1.6304  1.6978  1.7318  1.7476
g=0.50  max osc*g^2 at L=4,8,16,32,64: 0.5416  0.5822  0.6062  0.6182  0.6236
g=0.25  max osc*g^2 at L=4,8,16,32,64: 0.2977  0.3200  0.3330  0.3393  0.3418
g=0.10  max osc*g^2 at L=4,8,16,32,64: 0.2289  0.2457  0.2549  0.2584  0.2591
   (g=1/2, z=0.3+1e-3i, sigma=false, zeta=0), L=4,8,16,32,64: ['2.162', '2.320', '2.408', '2.441', '2.448']
== B. instance d=3 L=4 W=2 lam=1/2: n=L^d=64, N=(WL)^d=512
SB row sums min/max: 1.0 1.0
2.3 ThetaTilde_eq max abs err: 3.774758283725532e-15
J-coeff of Theta~ (alpha + 1/(n(1-T))) vs 1/(n(1-xi)): 0.03125 0.03125
sum_Stilde_row at zeta=ouZeta 1=0.632121: min/max row sum 1.000000000000 1.000000000000 (size 512)
Stilde_eq_SBtilde_mul max err: 0.0
ouVar diag=0.0196285825 Stilde_ii=0.0196285825 ; ouVar off=0.0098142913 Stilde_ij/2=0.0098142913
sigma=True xi=-0.5302-0.2822i |xi|=0.6006 osc(u=0,v=(1,0,0))=0.9278  g^-2*osc=0.2320 bulk |Re z|=0.50<=2-kappa=1.9
sigma=False xi=0.6006+0.0000i |xi|=0.6006 osc(u=0,v=(1,0,0))=1.1051  g^-2*osc=0.2763 bulk |Re z|=0.50<=2-kappa=1.9
== C. constants
ouTauMax(1/6,1/10)= 0.001388888888888889 =1/720: True
slack: 12tau=0.01667<=c=0.16667; 12tau<=c*d=0.01667; tau<c*d; 3tau/2=0.002083 < 2cd/3=0.011111 (margin 0.009028 = 13cd/24=0.009028)
Markov: eps=0.01 D=10 p=551  2p*eps=11.020 >= 1+eps+D=11.010
Markov: eps=0.001 D=100 p=50501  2p*eps=101.002 >= 1+eps+D=101.001
```
Reading of the output.
- (A) osc·g² is bounded and converges in L (increments 0.11, 0.07, 0.03, 0.02 for g = 1) with no log L growth; the dispatcher's row (ζ=0, g=1/2, z=0.3+10⁻³i, σ=false: 2.162, 2.320, 2.408, 2.441) is reproduced and extended (L=64: 2.448).
- (B) rows: ThetaTilde_eq holds to 4e-15; the J-coefficient of Θ̃ equals 1/(L^d(1−ξ)) (the Θ_ξ one), so Θ̃ − Θ_ξ has no zero-mode part; sum_Stilde_row, Stilde_eq_SBtilde_mul and the ouVar diagonal/off-diagonal identities hold; both σ give finite oscillation 0.93 and 1.11 at the instance, i.e. at most 0.28·lam⁻².
- (C) ouTauMax = 1/720 and the slack of row 7; Markov integers of row 12.
- Instance data of the pins: sz0 is Admissible (1/6, 1/10) in Lean (Sizes.lean:331 sz0_admissible); the limit checks (WL)^{1/2} ≤ W, W^{−1.4} ≤ lam ≤ 10, N → ∞, and η_Q ≥ N^{−1+2𝔠𝔡/3} are computed by the second script (below).
Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2276/sz0.py`; output (verbatim):
```
0 W>=N^(1/6): True ; W^(-1.4)=7.813e-03 <= lam=1.562e-02: True ; lam<=10 N=2.097e+06
    t*=4.838e-07 etaLL=4.909e-07 etaQ=1.202e-06 >= N^(-1+2cd/3)=5.605e-07: True ; etaQ<=1: True
1 W>=N^(1/6): True ; W^(-1.4)=6.104e-05 <= lam=2.441e-04: True ; lam<=10 N=5.498e+11
    t*=1.869e-12 etaLL=1.920e-12 etaQ=1.155e-11 >= N^(-1+2cd/3)=2.456e-12: True ; etaQ<=1: True
10 W>=N^(1/6): True ; W^(-1.4)=4.009e-10 <= lam=8.820e-09: True ; lam<=10 N=1.166e+25
    t*=9.086e-26 etaLL=9.626e-26 etaQ=5.287e-24 >= N^(-1+2cd/3)=1.629e-25: True ; etaQ<=1: True
1000 W>=N^(1/6): True ; W^(-1.4)=7.758e-24 <= lam=1.553e-20: True ; lam<=10 N=2.135e+60
    t*=5.381e-61 etaLL=6.183e-61 etaQ=1.182e-56 >= N^(-1+2cd/3)=2.192e-60: True ; etaQ<=1: True
```
- No external hypothesis is introduced: the hypotheses of the instances that stay open are the owed pins UNOULL, UNG1Row, UNG2bRow (other gates, vocabulary only in this ticket); Prop8ZeroMode is discharged by the merged prop5to8_holds (no hypothesis).

### Verdict per target (stage 1a)

- Target 1 (vocabulary), 2.1 to 2.3, 2.6, 2.7: PASS (algebraic identities confirmed on the instance; exponents of rows 7-12 close).
- Target 2.4 (d ≥ 3 oscillation, C(d,𝔡,κ)·lam⁻², no log L): PASS (follows from merged prop5to8_holds at t' = (1−ζ)lemT z ∈ [0,1); numeric consistency A and B).
- Target 2.5 (row differences): PASS (from 2.4, ‖ξ‖ ≤ 1).
- Target 3 (pins UNOULL, UNOUEq747, UNG1Row, UNG2bRow, definitions only): PASS (statements are Props; the instance keeps them as hypotheses).
- Target 4 (ouDiag_of_ouLL, ouRow_of_pins): PASS (Markov exponents of row 12; token match of the conclusions with UNOUDiag / UNOURow is a Lean check, not done here).
- Target 5 (instances): PASS (nondegenerate data above; no N = 0, no empty index, no collapsed window).
- Overall: PASS.

## (b) Script output — Tue Oct  6 09:37:31 UTC 2026

### Build, commit, scope
```
$ lake build RBM3D.Universality.ZeroModeProfile | tail -3

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (3737 jobs).
$ git log --oneline -1; git diff --stat main...t/T2276
33f413b T2276: UN-51a Universality/ZeroModeProfile (zero-mode profile S~, Theta~, d>=3 oscillation bound, layer pins, ouDiag_of_ouLL, ouRow_of_pins)
 RBM3D/Test/Axioms.lean                  |   5 +-
 RBM3D/Universality/ZeroModeProfile.lean | 806 ++++++++++++++++++++++++++++++++
 2 files changed, 809 insertions(+), 2 deletions(-)
$ wc -l RBM3D/Universality/ZeroModeProfile.lean; grep -cE "sorry|admit|native_decide|^axiom" (same file)
     806
0
```
Full `lake build` (with `import RBM3D.Universality.ZeroModeProfile` temporarily inserted after the UywKernel line of `RBM3D.lean`, then restored; not committed): `Build completed successfully (4083 jobs)`, root `#assert_rbm_axioms` ran. Registry pre-check (`import RBM3D` + `import RBM3D.Universality.ZeroModeProfile` + `#assert_rbm_axioms`, `lake env lean`): exit 0; ledger lines for the new pins:
```
1:axiom audit: 8025 theorems, 2634 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
107:  RBM.Univ.UNOULL: 3 [no certificate]
108:  RBM.Univ.UNG1Row: 3 [no certificate]
109:  RBM.Univ.UNG2bRow: 2 [no certificate]
```
### Axioms (`#print axioms`, all 43 public declarations of the file incl. instances)
```
lines printed:       43; lines ending with [propext, Classical.choice, Quot.sound]: 43
Stilde_zero : [propext, Classical.choice, Quot.sound]
sum_Stilde_row : [propext, Classical.choice, Quot.sound]
ouVar_eq_Stilde : [propext, Classical.choice, Quot.sound]
Stilde_eq_SBtilde_mul : [propext, Classical.choice, Quot.sound]
ThetaTilde_zero : [propext, Classical.choice, Quot.sound]
ThetaTilde_eq : [propext, Classical.choice, Quot.sound]
norm_ThetaTilde_sub_le : [propext, Classical.choice, Quot.sound]
profTilde_rowDiff : [propext, Classical.choice, Quot.sound]
profPMTilde_zero : [propext, Classical.choice, Quot.sound]
ouTauMax_pos : [propext, Classical.choice, Quot.sound]
ouTauMax_slack : [propext, Classical.choice, Quot.sound]
ouDiag_of_ouLL : [propext, Classical.choice, Quot.sound]
ouRow_of_pins : [propext, Classical.choice, Quot.sound]
```
### Scratch check (the check file + `import RBM3D.Universality.ZeroModeProfile`; examples `T2276_<name> := @RBM.Univ.<name>` for the 13 theorems, `@RBM.Univ.<v> = @RBM.Univ.T2276Check.<v> := rfl` for the 15 names of check sections 2-3)
```
$ lake env lean scratchpad/T2276/match.lean > match.out; echo $?  ->  0;  grep -c error match.out  -> 0
```
### Target statements (extracted by script from the file)
```lean
-- RBM3D/Universality/ZeroModeProfile.lean:158
theorem Stilde_zero (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ) (i j : Idx d L W) :
    Stilde d L W lam 0 i j = svarF d L W lam i j := by
-- RBM3D/Universality/ZeroModeProfile.lean:162
theorem sum_Stilde_row (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ) (hL : 3 ≤ L) (ζ : ℝ)
    (i : Idx d L W) : ∑ j, Stilde d L W lam ζ i j = 1 := by
-- RBM3D/Universality/ZeroModeProfile.lean:173
theorem ouVar_eq_Stilde (d L W : ℕ) [NeZero L] [NeZero W] (lam t : ℝ) (ht : 0 ≤ t)
    (c : CoordF d L W) :
    (ouVar d L W lam t c : ℝ) =
      if c.1 = c.2.1 then Stilde d L W lam (ouZeta t) c.1 c.2.1
      else Stilde d L W lam (ouZeta t) c.1 c.2.1 / 2 := by
-- RBM3D/Universality/ZeroModeProfile.lean:196
theorem Stilde_eq_SBtilde_mul (d L W : ℕ) [NeZero L] [NeZero W] (lam ζ : ℝ) (i j : Idx d L W) :
    (Stilde d L W lam ζ i j : ℂ) =
      SBtilde d L lam ζ (split d L W i).1 (split d L W j).1 * (((W : ℂ) ^ d)⁻¹) := by
-- RBM3D/Universality/ZeroModeProfile.lean:224
theorem ThetaTilde_zero (lam : ℝ) (ξ : ℂ) : ThetaTilde d L lam 0 ξ = Theta d L lam ξ := by
-- RBM3D/Universality/ZeroModeProfile.lean:281
theorem ThetaTilde_eq (lam : ℝ) (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) {ζ : ℝ} (h0 : 0 ≤ ζ)
    (h1 : ζ ≤ 1) :
    ThetaTilde d L lam ζ ξ = Theta d L lam (ξ * (1 - (ζ : ℂ))) +
      (ξ * ζ / ((L : ℂ) ^ d * (1 - ξ * (1 - (ζ : ℂ))) * (1 - ξ))) • Jmat d L := by
-- RBM3D/Universality/ZeroModeProfile.lean:367
theorem norm_ThetaTilde_sub_le :
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔡 κ : ℝ, 0 < 𝔡 → 0 < κ → ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ lam : ℝ, 0 < lam → lam ≤ 𝔡⁻¹ →
        ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → |z.re| ≤ 2 - κ → ∀ ζ : ℝ, 0 ≤ ζ → ζ ≤ 1 →
          ∀ (σ : Bool) (u v : Zd d L),
            ‖ThetaTilde d L lam ζ (xiQ z σ) u v - ThetaTilde d L lam ζ (xiQ z σ) 0 0‖ ≤
              C * (lam ^ 2)⁻¹ := by
-- RBM3D/Universality/ZeroModeProfile.lean:469
theorem profTilde_rowDiff :
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔡 κ : ℝ, 0 < 𝔡 → 0 < κ → ∃ C : ℝ, 0 < C ∧
      ∀ (sz : Sizes d) (n : ℕ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ →
        ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → |z.re| ≤ 2 - κ → ∀ ζ : ℝ, 0 ≤ ζ → ζ ≤ 1 →
          ∀ a b b' : Zd d (sz.L n),
            ‖profPMTilde sz n ζ z a b - profPMTilde sz n ζ z a b'‖ ≤
                C * (sz.lam n ^ 2)⁻¹ / ((sz.W n : ℕ) : ℝ) ^ d ∧
            ‖profPPTilde sz n ζ z a b - profPPTilde sz n ζ z a b'‖ ≤
                C * (sz.lam n ^ 2)⁻¹ / ((sz.W n : ℕ) : ℝ) ^ d := by
-- RBM3D/Universality/ZeroModeProfile.lean:522
theorem profPMTilde_zero {d : ℕ} (sz : Sizes d) (n : ℕ) (z : ℂ) (a b : Zd d (sz.L n)) :
    profPMTilde sz n 0 z a b = profPM sz n z a b ∧ profPPTilde sz n 0 z a b = profPP sz n z a b := by
-- RBM3D/Universality/ZeroModeProfile.lean:530
theorem ouTauMax_pos {𝔠 𝔡 : ℝ} (h𝔠 : 0 < 𝔠) (h𝔡 : 0 < 𝔡) : 0 < ouTauMax 𝔠 𝔡 := by
-- RBM3D/Universality/ZeroModeProfile.lean:536
theorem ouTauMax_slack {𝔠 𝔡 τU : ℝ} (h𝔠 : 0 < 𝔠) (h𝔡 : 0 < 𝔡) (h : τU ≤ ouTauMax 𝔠 𝔡) :
    12 * τU ≤ 𝔠 ∧ 12 * τU ≤ 𝔠 * 𝔡 ∧ τU < 𝔠 * 𝔡 ∧ 3 * τU / 2 < 2 * (𝔠 * 𝔡) / 3 := by
-- RBM3D/Universality/ZeroModeProfile.lean:641
theorem ouDiag_of_ouLL :
    ∀ {d : ℕ} {sz : Sizes d} {τU : ℝ}, UNOULL sz τU → UNOUDiag sz τU := by
-- RBM3D/Universality/ZeroModeProfile.lean:719
theorem ouRow_of_pins : UNG1Row → UNG2bRow → UNOURow := by
```
### Compiled nonempty instances (namespace `RBM.Univ.ZeroModeProfileInst`, signatures extracted by script; proofs in the file, lines 725-806)
```lean
theorem inst_sum_Stilde_row (i : Idx 3 4 2) : ∑ j, Stilde 3 4 2 (1 / 2) (ouZeta 1) i j = 1 :=
theorem inst_ouVar_eq_Stilde (i : Idx 3 4 2) :
    (ouVar 3 4 2 (1 / 2) 1 (i, i, true) : ℝ) = Stilde 3 4 2 (1 / 2) (ouZeta 1) i i := by
theorem inst_ThetaTilde_eq :
    ThetaTilde 3 4 (1 / 2) (1 / 100) (1 / 2 : ℂ) =
      Theta 3 4 (1 / 2) ((1 / 2 : ℂ) * (1 - (((1 / 100 : ℝ)) : ℂ))) +
        ((1 / 2 : ℂ) * ((1 / 100 : ℝ) : ℂ) /
          ((4 : ℂ) ^ 3 * (1 - (1 / 2 : ℂ) * (1 - (((1 / 100 : ℝ)) : ℂ))) * (1 - (1 / 2 : ℂ)))) •
          Jmat 3 4 := by
theorem inst_norm_ThetaTilde_sub_le : ∃ C : ℝ, 0 < C ∧ ∀ σ : Bool,
    ‖ThetaTilde 3 4 (1 / 2) (1 / 2) (xiQ ((1 / 2 : ℂ) + Complex.I / 2) σ) 0 (fun i => if i = 0 then 1 else 0) -
      ThetaTilde 3 4 (1 / 2) (1 / 2) (xiQ ((1 / 2 : ℂ) + Complex.I / 2) σ) 0 0‖ ≤
        C * ((1 / 2 : ℝ) ^ 2)⁻¹ := by
theorem inst_profTilde_rowDiff : ∃ C : ℝ, 0 < C ∧ ∀ a b b' : Zd 3 (sz0.L 0),
    ‖profPMTilde sz0 0 (1 / 2) ((1 / 2 : ℂ) + Complex.I / 2) a b -
        profPMTilde sz0 0 (1 / 2) ((1 / 2 : ℂ) + Complex.I / 2) a b'‖ ≤
      C * (sz0.lam 0 ^ 2)⁻¹ / ((sz0.W 0 : ℕ) : ℝ) ^ 3 := by
theorem inst_profPMTilde_zero (a b : Zd 3 (sz0.L 0)) (z : ℂ) :
    profPMTilde sz0 0 0 z a b = profPM sz0 0 z a b ∧ profPPTilde sz0 0 0 z a b = profPP sz0 0 z a b :=
theorem inst_ouTauMax : ouTauMax (1 / 6) (1 / 10) = 1 / 720 := by
theorem inst_ouTauMax_slack :
    12 * (1 / 1000 : ℝ) ≤ 1 / 6 ∧ 12 * (1 / 1000 : ℝ) ≤ 1 / 6 * (1 / 10) ∧
      (1 / 1000 : ℝ) < 1 / 6 * (1 / 10) ∧ 3 * (1 / 1000 : ℝ) / 2 < 2 * (1 / 6 * (1 / 10)) / 3 :=
theorem inst_ouDiag : UNOULL sz0 (1 / 1000) → UNOUDiag sz0 (1 / 1000) :=
theorem inst_g1 (r1 : UNG1Row) (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand) (hQ : UNQueBand) :
    UNOULL sz0 (1 / 1000) ∧ UNOUEq747 sz0 (1 / 10) (1 / 1000) :=
theorem inst_ouRow (r1 : UNG1Row) (r2b : UNG2bRow) : UNOURow :=
```
### Name-clash grep
```
$ grep -rnw (each of the 15 vocabulary/pin names, 13 theorem names, 4 ouZeta lemmas, ZeroModeProfileInst) RBM3D RBM3D.lean, excluding the new file:
hits only in RBM3D/Test/Axioms.lean:204-206 (this ticket's registry lines: UNOULL, UNG1Row, UNG2bRow; ouDiag_of_ouLL, ouRow_of_pins appear in their comments)
$ git --no-optional-locks grep -nwE "<same names>" main -- RBM3D RBM3D.lean   ->  (no output)
```
### Port (RBM2D, read-only)
```
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h  -> 9e0f275
source: RBM2D/Universality/ZeroModeProfile.lean at c9a24cf (via git show), 1269 lines
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Universality/ZeroModeProfile.lean
 RBM2D/Universality/ZeroModeProfile.lean | 851 +++-----------------------------
 1 file changed, 63 insertions(+), 788 deletions(-)
```

### Narrative (Tue Oct  6 09:37:54 UTC 2026)
- Ported from RBM2D `ZeroModeProfile.lean` (c9a24cf) as the ticket maps it: §1 `:46-196` (`ouZeta`, `Stilde`, `sum_Stilde_row`, `ouVar_eq_Stilde`, `ouZeta` lemmas), §2 `:205-394` (`Jmat`, `SBtilde`, `ThetaTilde`, J-algebra, `ThetaTilde_eq`), `Stilde_eq_SBtilde_mul` `:405`, §5 `:550-698` (`eventually_forall_mem_of_forall_seq'` verbatim, Markov step, `ouDiag_of_ouLL`), §6 `:715` (`ouRow_of_pins`).
- Replaced at `d ≥ 3`: `norm_ThetaTilde_sub_le` (copy of `thetaDiff` `QUECore.lean:105-170` and private `theta_diff_of_row` `:87`, at `t' = (1 - ζ) lemT z`, constant `2 C₈`, no `log L`); `profTilde_rowDiff` (from 2.4, `‖ξ‖ ≤ 1`); `ouTauMax`, `ouEtaLL`, `ouEtaQ`, the four pins and the profiles `profPMTilde`/`profPPTilde` are the check file's texts verbatim (statement match: `match.lean` exit 0).
- Imports: `Universality.OU`, `Endpoints`, `Propagator.Prop6Hold`, `Green.IBP` (`IBP_sum_svarF_row` used, not copied), `Path.Walk` (`walk_measurable_Gres_apply`, instead of porting RBM2D's `_measurable_inv_entry`), `Induction.Split` (`RBM.Ind.norm_apply_le_l2_opNorm`; `norm_Gsig_le_inv_eta` is in its import `Gauss.FlowCalculus`). `Universality.OUHessian` is not imported (no name used); no `Main.*`, `Graph.*`, or root import.
- One proof-level difference from RBM2D: `ouDiag_of_ouLL` splits at `2 < κ` (the vacuous case), not `2 ≤ κ`, because `UNOUDiag` has `|E| ≤ 2 - κ` and `E = 0` is admissible at `κ = 2`; that case goes through the general branch (`T n` contains `(0,0)`). No statement is affected.
- `Test/Axioms.lean`: by text, the lines `UNOUDiag` and `UNOURow` of `owedProps` are deleted and `UNOULL`, `UNG1Row`, `UNG2bRow` are added (3 inserted, 2 deleted: see diff stat). `UNOUEq747` has no line (ticket). Owed count: -2 + 3.
- Instances (§7): every deterministic hypothesis is discharged by `norm_num`/`simp` at `d = 3`, `L = 4`, `W = 2`, `lam = 1/2` (and at `sz0`, `n = 0` for 2.5); `UNOULL`, `UNG1Row`, `UNG2bRow` stay hypotheses (`inst_ouDiag`, `inst_g1`, `inst_ouRow`); `inst_g1` uses `sz0_admissible` and `τ_U = 1/1000 ≤ ouTauMax (1/6) (1/10) = 1/720` (`inst_ouTauMax`).
- Not proved here (as the ticket's "Not targets"): `UNOULL`, `UNOUEq747`, `UNG1Row`, `UNG2bRow` (definitions only); RBM2D `trGEGEmat`, `card_sbSupport_lt_sq`, the 5-point `Stilde_le`, off-band lemma, `oueq747_zero_of_qdiff`, `integral_ouMat_zero`, `tendsto_*`, `half_le_ouZeta`, `Stilde_one` are not ported.
- Special cases / generality: 2.4 is for the two profile parameters `ξ ∈ {m², |m|²}` only (`xiQ`), bulk, `0 < lam ≤ 𝔡⁻¹`; `profTilde_rowDiff` likewise. `ouDiag_of_ouLL` is conditional on `UNOULL`; `ouRow_of_pins` on `UNG1Row`, `UNG2bRow`.

## (c) Verified Mathlib names used (all by compilation of the file)
`Ring.mul_inverse_cancel`, `mul_eq_one_comm`, `Complex.mul_conj`, `Complex.normSq_eq_norm_sq`, `Complex.norm_real`, `Complex.norm_natCast`, `Real.coe_toNNReal`, `NNReal.coe_inv`, `NNReal.coe_natCast`, `Real.exp_le_one_iff`, `Real.add_one_le_exp`, `inv_anti₀`, `inv_le_one_of_one_le₀`, `one_le_pow₀`, `div_le_div_of_nonneg_right`, `pow_le_pow_left₀`, `mul_meas_ge_le_integral_of_nonneg`, `ofReal_measureReal`, `measure_iUnion_fintype_le`, `measure_mono`, `Integrable.of_bound`, `Measurable.pow_const`, `Real.rpow_le_rpow_of_exponent_le`, `Nat.le_ceil`, `min_def`, `Filter.not_eventually`, `Filter.Frequently.and_eventually`. Names verified absent: none searched.
RBM3D names used: `IBP_sum_svarF_row`, `RBM.Gauss.card_Idx`, `Sizes.card_Idx`, `svarF`, `SB_eq_map_SBR`, `sum_SB_row`, `SB_transpose`, `norm_SB`, `Theta_mul`, `Theta_apply_add_right`, `Theta0_apply`, `one_sub_ne_zero`, `prop5to8_holds`, `lemma28_quant`, `mE_lemE`, `norm_msc_lt_one`, `lemT_lt_one`, `walk_measurable_Gres_apply`, `measurable_ouMat`, `ouMat_isHermitian`, `norm_Gsig_le_inv_eta`, `RBM.Ind.norm_apply_le_l2_opNorm`, `sz0_admissible`.

## (d) Open issues and paper-delta candidates
- T2276a (design, as in the ticket): the `d ≥ 3` interface is `UNOULL` plus `UNOUEq747` in the shape of `QDiff`'s expectation half at `η_Q = etaQ sz n (𝔡/3)` with `Θ̃`; `UNG1Row` takes the three inputs of `UNOURow`. Implemented as pinned; no change.
- T2276b: `ouTauMax 𝔠 𝔡 = min (𝔠/12, 𝔠𝔡/12, 1/100)`, slack by `ouTauMax_slack`. Implemented as pinned; whether UN-51's binding inequalities hold at this value is not checked here (ticket preflight (vi) is for UN-51).
- Observation: RBM2D `ZeroModeProfile.lean` at HEAD (9e0f275) differs from c9a24cf (diff-stat above); the port follows c9a24cf as the ticket specifies.
- No statement difference from the ticket's check file found; no T2276c.
