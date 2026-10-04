Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 17:37:12 UTC 2026

Target 1 (`stTailtoTail_holds d : STTailtoTail d`, `Step5Pins.lean:121`): for `3 ≤ d`, `L ≥ 3`, `g,W > 0`, `D` real, `0 ≤ s ≤ t < 1`, `g² ≤ 1−t`, `‖m‖ = 1`, `σ : Fin 2 → Bool`, `‖A b‖ ≤ tailTD d W s D (zdistInf (b 0 − b 1))`:
`‖UN d L g (EKsgn m σ) s t A a‖ ≤ C·tailTD d W t D (zdistInf (a 0 − a 1)) + ((1−s)/(1−t))² W^{−D}`,
`tailTD d W u D r = ((W^d|1−u|)⁻¹)²·e^{−√r} + W^{−D}` (`Defs/Tail.lean:173`).

### (i) Route and exponent table

Route (merged names, file:line in `main` 3b1c6a5). Notation `ρ = (1−s)/(1−t) ≥ 1`, `S = SB d L g`, `Θ_ξ = Theta d L g ξ`, `w(x) = e^{c·zdistInf x}`.
1. `UN` (`Kernel/Evolution.lean:65`) for `n = 2` is `Σ_b uKer(μ₀)(a 0)(b 0)·uKer(μ₁)(a 1)(b 1)·A b`, with `μ_i = cycProd (EKsgn m σ) i` (`:49`), `μ₀ = μ₁ = m_{σ₀}m_{σ₁} =: μ`, `‖μ‖ = 1` (`norm_cycProd` `:73`, `ek_norm_spin` `Evolution/Pins.lean:47`).
2. Entry domination. `uKer μ s t = (s/t)·1 + ((t−s)/t)·Θ_{tμ}` for `t > 0` (from `(1−tμS)Θ = 1`, `mul_Theta_of_three_le` `Props4.lean:90`; `t = 0` forces `s = 0`, `uKer = 1`); `|Θ_{tμ}(a,b)| ≤ (Θ_t(a,b)).re` (`norm_Theta_apply_le` `Props4.lean:188`), `(Θ_t).re ≥ 0` (`:177`), row sum `(1−t)⁻¹` (`sum_Theta_real_row` `:203`). So `Q(a,b) := |uKer μ s t a b| ≤ (s/t)1_{a=b} + ((t−s)/t)(Θ_t(a,b)).re`, row sums `≤ ρ` (this is `norm_uKer_le` `Evolution.lean:114` with `sum_norm_row_le` `:78`).
3. Amplitude identity (exact): `ρ²(W^d(1−s))⁻² = (W^d(1−t))⁻²`; `|1−u| = 1−u` as `u < 1`.
4. Triangle: `zdistInf (a0−a1) ≤ zdistInf (a0−b0) + zdistInf (b0−b1) + zdistInf (b1−a1)` (coordinatewise `zdist_add_le`; the merged copies are `private`, e.g. `PropTInf.lean:43`, so copy as `tailtoTail_zdistInf_add_le`), then `√(x+y+z) ≤ √x+√y+√z`. Hence `e^{−√|b0−b1|} ≤ e^{−√|a0−a1|}·e^{√|a0−b0|}·e^{√|a1−b1|}`.
5. Weighted Neumann bound (replaces the Fable `q^{|x|₁}` pointwise bound; no torus lifts needed). `Σ_y S(a,y)w(a−y) = S(a,a) + e^c·Σ_{y~a}S ≤ 1 + (e^c−1)·2dg²/(1+2dg²) =: λ` (neighbours have `zdistD = 1`, `Block.lean:38`, so `zdistInf ≤ 1`, `zdistInf_le_zdistD` `Sizes.lean:117`; mass `2dg²/(1+2dg²)` from `card_nbhd`/`sum_sbKernelR` `Block.lean:93`). Submultiplicativity `w(a−b) ≤ w(a−c)w(c−b)` (step 4 triangle) and induction on `k`: `Σ_b (S^k)(a,b)w(a−b) ≤ λ^k`. With `Θ_t(a,b) = Σ_k t^k (S^k)(a,b)` (`Theta_real_eq_tsum` `Props4.lean:166`, `SBR_pow_nonneg` `:62`): `Σ_b Θ_t(a,b)w(a−b) ≤ 1/(1−tλ)`.
6. With `c = 1/(4d+1)`: `e^c ≤ 1/(1−c)` so `e^c−1 ≤ 1/(4d)`; `g² ≤ 1−t` gives `tλ ≤ t + t·2d g²(e^c−1) ≤ t + (1−t)/2`, i.e. `1−tλ ≥ (1−t)/2`, `Σ_bΘ_t(a,b)w(a−b) ≤ 2/(1−t)`. Then `Σ_b Q(a,b)w(a−b) ≤ [(s/t) + ((t−s)/t)·2/(1−t)] = 2ρ` (since `s(1−t)+(t−s) = t(1−s)`).
7. `√r ≤ c·r + 1/(4c)` (AM–GM): `e^{√r} ≤ e^{(4d+1)/4} w`. So `Σ_b Q(a,b)e^{√|a−b|} ≤ 2ρ·e^{(4d+1)/4}`. Translation invariance (`SB_apply_add_right` `Block.lean:62`, `Theta_apply_add_right_of_three_le` `Props4.lean:100`) is only needed to reindex; the bound holds for each `a` as stated.
8. Assemble. `|UN A (a)| ≤ Σ_b Q(a0,b0)Q(a1,b1)·T_{s,D}(|b0−b1|)`. Main part `≤ (W^d(1−s))⁻² e^{−√|a0−a1|}(2ρ e^{(4d+1)/4})² = 4e^{(4d+1)/2}·(W^d(1−t))⁻² e^{−√|a0−a1|}` (step 3). The `W^{−D}` part is `≤ ρ² W^{−D}` (row sums `≤ ρ`, step 2). The main part is `≤ C·tailTD d W t D (…)` as the `W^{−D}` summand of `tailTD` is `≥ 0` (`W > 0`).
9. `σ₁ = σ₂` or not is irrelevant: only `‖μ‖ = 1` is used (step 2, property 4). No `ThetaDecay` hypothesis, no `ℓ_t`, no `B_{t,r}`.

Exponent/constant table (d = 3 numbers):

| quantity | value / constraint | slack |
|---|---|---|
| `ρ = (1−s)/(1−t)` | `≥ 1`; row sum of `Q` `≤ ρ` | equality at `A ≡ 1` (rows of `P^{(+,−)}` sum to ρ, instance below) |
| amplitude `ρ²(W^d(1−s))⁻² = (W^d(1−t))⁻²` | identity | 0 (exact) |
| `c = 1/(4d+1)` | need `e^c−1 ≤ 1/(4d)` | d=3: `0.079959 ≤ 0.083333`, slack `3.4e−3` |
| `λ ≤ 1+(e^c−1)·2dg²/(1+2dg²)` | `1−tλ ≥ (1−t)/2` uses `g² ≤ 1−t` | boundary `g²=1−t=0.01`, d=3: `0.005519 ≥ 0.005` |
| `Σ_bΘ_t w ≤ 1/(1−tλ) ≤ 2/(1−t)` | | boundary: `109.28 ≤ 181.18 ≤ 200` |
| `√r ≤ cr + 1/(4c)` | factor `e^{1/(4c)} = e^{(4d+1)/4}` | d=3: `e^{3.25} = 25.79` |
| `C = 4e^{(4d+1)/2}` | `C ≥ (2e^{(4d+1)/4})²`; depends on `d` only | d=3: `C = 2660.57`; worst observed ratio `1.36` (iii) |
| variant without `s/t` form | `Σ Q w ≤ 1+(t−s)λ/(1−tλ) ≤ (5/2)ρ`, `C' = 7e^{(4d+1)/2}` | also valid (`λ ≤ 1+1/(4d) ≤ 5/4`) |
| `t < 1`, `0 ≤ s ≤ t`, `L ≥ 3`, `g > 0`, `W > 0`, `D ∈ ℝ` | needed for `Θ_t` series, `NeZero L`, `norm_SB`, `W^{−D} ≥ 0` | |
| Fable `q = 2dtg²/(1+2dg²−t) ≤ 2d/(2d+1)` | alternative pointwise route; crude `C_3 ≈ 3.6e5` per Fable; needs torus `ℓ¹` lifts | not used |

(ii)-extra, rerun of the Fable scripts at d = 3 (copied to the scratchpad `T2147/`, unmodified; sizes L = 16, 32, 64 and the 18 `(L, g, 1−s, 1−t)` rows of their regime table):
```
$ python3 check_neiwuj.py > out_neiwuj.txt   # = docs/claude-team/fable/2026-10-04-tailtotail-check_neiwuj.py
$ awk '/regime of the lemma/{f=1} /OUTSIDE/{f=0} f&&/paper T_/{n=split($0,a,"max"); v=a[n]+0; if(v>m)m=v} END{print "worst paper-T ratio in lemma regime:",m}' out_neiwuj.txt
worst paper-T ratio in lemma regime: 1.36
$ python3 check_extra.py > out_extra.txt; tail -4 out_extra.txt | cut -c1-120
=== (4) literal (neiwuj) with W, D: (U o T_{s,D})(a) <= 1.4 T_{t,D}(|a1-a2|) + rho^2 W^{-D} ? ===
L=16 W=10 D=5.0 g=0.1 1-s=0.5 1-t=0.01: holds everywhere: True; max (U T_s)/(T_t + rho^2 W^-D) = 1.0075
L=16 W=10 D=8.0 g=0.01 1-s=0.5 1-t=0.0001: holds everywhere: True; max (U T_s)/(T_t + rho^2 W^-D) = 1.3456
L=16 W=100 D=12.0 g=0.3 1-s=0.9 1-t=0.09: holds everywhere: True; max (U T_s)/(T_t + rho^2 W^-D) = 1.2546
```
Worst ratio LHS/RHS of `(neiwuj)` (`T_{u,D}` main part, exact `U^{(2)}` by FFT, dense `L=6` cross-check agrees): `1.360` (g = 0.01, 1−s = 0.5, 1−t = 1e−4 = g², L = 16, r = L/2), versus the constant `C = 2660.57`. Same `1.36` as the Fable report. Output reproduces `docs/claude-team/fable/2026-10-04-tailtotail-output.txt` lines for the regime table (identical numbers); the pin is true as stated at d = 3 in every tried case, three unit values of `μ` (1, `e^i`, −1) in the check below: `max(|P^μ|−P^{(+,−)}) ≤ 2.2e−16`).

### (ii) One concrete nondegenerate instance

Ticket instance: `d = 3, L = 3, g = 1/2, W = 2, s = 0, t = 1/2, A = 0`; add `D = 2`, `m` with `‖m‖ = 1` (`μ = 1`, `e^{i}`, `−1` checked), any `σ`. Hypotheses: `3 ≤ L` (3 ≤ 3); `g, W > 0`; `0 ≤ 0 ≤ 1/2 < 1`; `g² = 1/4 ≤ 1−t = 1/2` (slack 1/4); `ρ = 2`; `A = 0` satisfies `‖A b‖ = 0 ≤ tailTD` (`tailTD ≥ 0`, `tailTD_nonneg`); conclusion `0 ≤ C·tailTD + 4·2^{−2}`. Not collapsed: `L^d = 27` points, `A` bound has `T_{s,D} ≥ W^{−D} = 1/4 > 0`. Script `inst.py` (scratchpad `T2147/`, dense 27×27 and 64×64/125×125 matrices, `P = (1−sμS)(1−tμS)⁻¹`), checks the proof steps 2, 5–8 at the instance and at three boundary cases `g² = 1−t`:
```
$ python3 inst.py | cut -c1-175   (lines trimmed to the claims)
INSTANCE(m=1): d=3 L=3 g=0.5 W=2.0 D=2.0 s=0.0 t=0.5 rho=2.0000 g^2<=1-t:True
   rowsum Prow(+-)=2.000000=rho; min P(+-)=3.04e-03; max(|P^mu|-P^(+-))=2.22e-16
   lambda_c=1.047975<=1.047975; 1-t*lam=0.476012>=(1-t)/2=0.250000; sum Th w=2.0573<=1/(1-t lam)=2.1008<=2/(1-t)=4.0000
   sum_x|P(0,x)|e^sqrt|x| = 3.2313 <= e^((4d+1)/4)*2rho = 103.1614
   worst main-part ratio (|P|x|P|)(T_s main)/T_t main = 1.1061 <= C=4e^((4d+1)/2)=2660.6; worst ratio to (T_t+rho^2W^-D)=0.8055
INSTANCE(mu=e^i): ... max(|P^mu|-P^(+-))=-1.87e-03; sum_x|P(0,x)|e^sqrt|x| = 2.3060 <= 103.1614; main ratio 0.6480
INSTANCE(mu=-1):  ... max(|P^mu|-P^(+-))=-2.74e-03; sum_x|P(0,x)|e^sqrt|x| = 1.4907 <= 103.1614; main ratio 0.3174
boundary g^2=.09=1-t: L=4 g=0.3 W=5 D=4 s=0.2 t=0.91 rho=8.8889: 1-t*lam=0.064486>=0.045000; main ratio 0.0649; sum|P|e^sqrt=3.5627<=458.49
boundary g^2=.04=1-t, s=0: L=5 g=0.2 t=0.96 rho=25: 1-t*lam=0.025143>=0.020000; main ratio 0.0010; sum|P|e^sqrt=0.9218<=1289.5
boundary g^2=.01=1-t: L=4 g=0.1 W=3 D=3 s=0.5 t=0.99 rho=50: 1-t*lam=0.005519>=0.005000; main ratio 1.2628; sum|P|e^sqrt=141.44<=2579.0
C(d=3) = 2660.5665321774472  c=1/13, e^c-1= 0.07995899942818663  <= 1/(4d)= 0.08333333333333333
```
External hypotheses: none (no `ThetaDecay`, `ThetaDecayShort` or `Step2LocalPT` in the route; nothing needs a limit computation). The only analytic inputs are merged and proved: `norm_Theta_apply_le`, `Theta_real_eq_tsum`, `norm_SB`/`card_nbhd`, `uKer_eq_one_add`/`norm_uKer_le`.

### Verdict
- Target 1 `stTailtoTail_holds`: **PASS**. The merged pin is true as pinned (no case of `σ`, constant or floor term fails; `W^{−D}` floor gives exactly the `ρ²W^{−D}` term), `C = 4e^{(4d+1)/2}` depends on `d` only, the instance above has every hypothesis discharged. Risk notes for stage 1b (not defects): (1) the `√` and `zdistInf` triangle lemmas are `private` in other files and must be copied with the `tailtoTail_` prefix; (2) `Σ_{b : Fin 2 → Zd d L}` must be split into `Σ_{b0}Σ_{b1}`; (3) the `t = 0` case (then `s = 0`, `uKer = 1`) must be separated from the `s/t` form or use the variant of the table (`C' = 7e^{(4d+1)/2}`), which has no division by `t`.
- Target 2 (compiled instances `stTailtoTail_holds 3` and the bound at `d=3, L=3, g=1/2, W=2, s=0, t=1/2, A=0`): **PASS** (hypotheses above hold simultaneously).

## (a′) Preflight corrections — Sun Oct  4 17:49:35 UTC 2026

No verdict changes; two route/constant differences from (a), both read off the committed file (`58abe97`):
- Constant. The proof gives `C = (3 e^{(4d+1)/4})² = 9 e^{(4d+1)/2}` (d = 3: 5986.27, `const.py` below), not the `4 e^{(4d+1)/2}` of the table row `C`. The pin only asks for `C > 0` depending on `d` alone.
- Route. (a) steps 2, 5, 6 are not followed literally. There is no `s/t` form and no `t = 0` split: `tailtoTail_ker_entry` bounds `‖(1 - sμS)Θ_{tμ}(a,b)‖ ≤ 1_{a=b} + (t-s)(SΘ_t)(a,b)` from `uKer_eq_one_add` and `norm_Theta_apply_le`. The Neumann series (`Theta_real_eq_tsum`) is replaced by the resolvent identity `Θ_t = 1 + tΘ_tS` (`Theta_mul_of_three_le`, `tailtoTail_theta_eq`); `tailtoTail_theta_wt` gives `Σ_b Θ_t(a,b)w(a-b) ≤ 2/(1-t)`, and `tailtoTail_ker_wt` gives `Σ_b|K(a,b)|w(a-b) ≤ 1 + 3(t-s)/(1-t) ≤ 3ρ`.

## (b) Script output

### Build, axioms, hygiene (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2147`, branch `t/T2147`)
```
$ git log -1 --format="%h %an <%ae> %s"
58abe97 Jun Yin <321276894+JYin80@users.noreply.github.com> T2147: S5-04 Induction/TailtoTail (proves STTailtoTail)
$ lake build RBM3D.Induction.TailtoTail 2>&1 | tail -2
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3775 jobs).
$ grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Induction/TailtoTail.lean
0
$ lake env lean scratchpad/T2147/axioms.lean   (import RBM3D.Induction.TailtoTail; #print axioms ...)
'RBM.Gauss.Sizes.stTailtoTail_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.inst_tailtoTail_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.inst_tailtoTail_extremal' depends on axioms: [propext, Classical.choice, Quot.sound]
$ git diff --stat main...t/T2147
 RBM3D/Induction/TailtoTail.lean | 628 ++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean          |   1 -
 2 files changed, 628 insertions(+), 1 deletion(-)
```

### Registry pre-check and full build (DECISIONS §16, §20; the hub adds the root import at merge, so it is added here temporarily and removed again, `git status --short` clean at the end)
```
$ git diff main...t/T2147 -- RBM3D/Test/Axioms.lean | grep "^[-+] "
-   `RBM.Gauss.Sizes.STTailtoTail, -- `(neiwuj)`, `tailtoTail` with the tail `T_{u,D}`: S5-04; S5-01 (T2138, DECISIONS §40: owed)
$ lake build            # root as committed (no import of the new module)
exit=1 (scratchpad/T2147/fullA.txt):
error: RBM3D.lean:192:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`:
  [RBM.Gauss.Sizes.STTailtoTail]
$ lake build            # root with `import RBM3D.Induction.TailtoTail` after the last import
exit=0 (scratchpad/T2147/fullB.txt):
info: RBM3D.lean:193:0: axiom audit: 4487 theorems, 1577 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (3894 jobs).
```

### Target 1: the pin and the theorem (extracted by `sed -n`)
```
$ sed -n 121,129p RBM3D/Induction/Step5Pins.lean     # the merged pin, unchanged
def STTailtoTail (d : ℕ) : Prop :=
  3 ≤ d → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) (_hL : 3 ≤ L) (g W D s t : ℝ), 0 < g → 0 < W → 0 ≤ s → s ≤ t → t < 1 → g ^ 2 ≤ 1 - t →
      ∀ m : ℂ, ‖m‖ = 1 → ∀ σ : Fin 2 → Bool, ∀ A : (Fin 2 → Zd d L) → ℂ,
        (∀ b, ‖A b‖ ≤ tailTD d W s D (zdistInf d L (b 0 - b 1) : ℝ)) →
        haveI : NeZero L := ⟨by omega⟩
        ∀ a, ‖UN d L g (EKsgn m σ) s t A a‖ ≤
          C * tailTD d W t D (zdistInf d L (a 0 - a 1) : ℝ) + ((1 - s) / (1 - t)) ^ 2 * W ^ (-D)

$ sed -n 582,591p RBM3D/Induction/TailtoTail.lean
theorem stTailtoTail_holds (d : ℕ) : STTailtoTail d := by
  intro hd
  refine ⟨(3 * Real.exp ((4 * (d : ℝ) + 1) / 4)) ^ 2, by positivity, ?_⟩
  intro L hL g W D s t hg hW hs hst ht hgt m hm σ A hA
  have : NeZero L := ⟨by omega⟩
  intro a
  exact tailtoTail_main hL (by omega) hW hs hst ht hgt hm σ A hA a

/-! ### 6. Instances (CLAUDE.md §4 step 2) -/

```

### Compiled nonempty instances (same file, lines 593-627; all hypotheses discharged by `norm_num`/`simp`, nothing left open)
```
$ sed -n 593,627p RBM3D/Induction/TailtoTail.lean
example : STTailtoTail 3 := stTailtoTail_holds 3

/-- **`TailtoTail`, instantiated** at `d = 3`, `L = 3`, `g = 1/2`, `W = 2`, `D = 2`, `s = 0`, `t = 1/2` (`g² = 1/4 ≤ 1/2 = 1 - t`;
`ρ = 2`), `m = i` (`|m| = 1`), `σ = (+,-)`, `A = 0` (`|A_b| = 0 ≤ T_{0,2}`), at `a = (0, e₁)`; the `27` points of `Z_3^3` are not collapsed. -/
theorem inst_tailtoTail_zero :
    ∃ C : ℝ, 0 < C ∧
      ‖UN 3 3 (1 / 2 : ℝ) (EKsgn Complex.I ![true, false]) (0 : ℝ) (1 / 2 : ℝ)
          (fun _ : Fin 2 → Zd 3 3 => (0 : ℂ)) ![0, ![1, 0, 0]]‖ ≤
        C * tailTD 3 2 (1 / 2 : ℝ) 2 (zdistInf 3 3 ((![0, ![1, 0, 0]] : Fin 2 → Zd 3 3) 0 -
            (![0, ![1, 0, 0]] : Fin 2 → Zd 3 3) 1) : ℕ) +
          ((1 - 0 : ℝ) / (1 - 1 / 2 : ℝ)) ^ 2 * (2 : ℝ) ^ (-(2 : ℝ)) := by
  obtain ⟨C, hC, H⟩ := stTailtoTail_holds 3 (by norm_num)
  refine ⟨C, hC, ?_⟩
  exact H 3 (by norm_num) (1 / 2) 2 2 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) Complex.I (by simp) ![true, false]
    (fun _ : Fin 2 → Zd 3 3 => (0 : ℂ))
    (fun b => by rw [norm_zero]; exact tailTD_nonneg (by norm_num)) ![0, ![1, 0, 0]]

/-- The same parameters with the extremal (nonzero) tensor `A_b = T_{s,D}(|b₁-b₂|)`. -/
theorem inst_tailtoTail_extremal :
    ∃ C : ℝ, 0 < C ∧
      ‖UN 3 3 (1 / 2 : ℝ) (EKsgn Complex.I ![true, false]) (0 : ℝ) (1 / 2 : ℝ)
          (fun b : Fin 2 → Zd 3 3 => ((tailTD 3 2 (0 : ℝ) 2 (zdistInf 3 3 (b 0 - b 1) : ℕ) : ℝ) : ℂ))
          ![0, ![1, 0, 0]]‖ ≤
        C * tailTD 3 2 (1 / 2 : ℝ) 2 (zdistInf 3 3 ((![0, ![1, 0, 0]] : Fin 2 → Zd 3 3) 0 -
            (![0, ![1, 0, 0]] : Fin 2 → Zd 3 3) 1) : ℕ) +
          ((1 - 0 : ℝ) / (1 - 1 / 2 : ℝ)) ^ 2 * (2 : ℝ) ^ (-(2 : ℝ)) := by
  obtain ⟨C, hC, H⟩ := stTailtoTail_holds 3 (by norm_num)
  refine ⟨C, hC, ?_⟩
  exact H 3 (by norm_num) (1 / 2) 2 2 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) Complex.I (by simp) ![true, false]
    (fun b : Fin 2 → Zd 3 3 => ((tailTD 3 2 (0 : ℝ) 2 (zdistInf 3 3 (b 0 - b 1) : ℕ) : ℝ) : ℂ))
    (fun b => by
      rw [Complex.norm_real, Real.norm_of_nonneg (tailTD_nonneg (by norm_num))]) ![0, ![1, 0, 0]]

```
Data: d = 3, L = 3 (27 points), g = 1/2, W = 2, D = 2, s = 0, t = 1/2 (g² = 1/4 ≤ 1/2 = 1-t, ρ = 2), m = i, σ = (+,-), a = (0, e₁); `inst_tailtoTail_zero` has A = 0 (the ticket instance), `inst_tailtoTail_extremal` has the nonzero extremal A_b = T_{0,2}(|b₁-b₂|) ≥ W^{-D} = 1/4.

### Name-clash grep (new public names `stTailtoTail_holds`, `inst_tailtoTail_zero`, `inst_tailtoTail_extremal`; private helpers carry the prefix `tailtoTail_`)
```
$ git -C /Users/junyin/Lean_proof/RBM3D grep -n "stTailtoTail_holds\|inst_tailtoTail_zero\|inst_tailtoTail_extremal\|tailtoTail_" main -- RBM3D | wc -l
       0
$ grep -c "^private" RBM3D/Induction/TailtoTail.lean; grep -c "^private [a-z]* tailtoTail_\|^private noncomputable def tailtoTail_" RBM3D/Induction/TailtoTail.lean
20
20
```

### Constants (`scratchpad/T2147/const.py`)
```
$ python3 const.py
d=3: c=1/(4d+1)=0.076923  d*(e^c-1)=0.239877 <= 1/4  ;  C=(3e^((4d+1)/4))^2=5986.27
d=4: c=1/(4d+1)=0.058824  d*(e^c-1)=0.242352 <= 1/4  ;  C=(3e^((4d+1)/4))^2=44232.92
d=5: c=1/(4d+1)=0.047619  d*(e^c-1)=0.243855 <= 1/4  ;  C=(3e^((4d+1)/4))^2=326839.52
d=10: c=1/(4d+1)=0.024390  d*(e^c-1)=0.246901 <= 1/4  ;  C=(3e^((4d+1)/4))^2=7199119597.28
instance: g^2=0.250 <= 1-t=0.500 ; rho=2.000 ; sum_x S(x)w(x) <= 1+g^2/2 = 1.1250 ; 1-t*lam >= (1-t)/2: 0.4375 >= 0.2500
```

### Ports
None. No text was copied from `../RBM1D` or `../RBM2D` (nothing read there, nothing run there): every lemma is new; RBM1D/RBM2D diff-stat not applicable.

### Narrative
- Statement: `stTailtoTail_holds d : STTailtoTail d` has the merged pin as its type; `Step5Pins.lean` is untouched. The only hypothesis used from `3 ≤ d` is `1 ≤ d`.
- Constant: `C = (3 e^{(4d+1)/4})²`, independent of `L, g, W, D, s, t, m, σ, A, a`. No external hypothesis (`ThetaDecay`, `ThetaDecayShort`, `Step2LocalPT`) occurs; the inputs are merged and proved: `uKer_eq_one_add`, `norm_uKer_le`, `norm_cycProd`, `ek_norm_spin`, `norm_Theta_apply_le`, `Theta_real_nonneg`, `Theta_mul_of_three_le`, `sum_sbKernelR`, `card_nbhd`, `zdistInf_le_zdistD`.
- Proof (helpers lines 91-455, assembly `tailtoTail_main` lines 458-580): `K_i = uKer (cycProd (EKsgn m σ) i) s t`, each with `‖cycProd‖ = 1`, so σ enters only through `‖μ‖ = 1` (σ₁ = σ₂ or not is not distinguished). `UN` is split into `Σ_{b₀} Σ_{b₁}` by `piFinTwoEquiv`; `tailTD` is split as `α e^{-√r} + W^{-D}`; the triangle inequality (`tailtoTail_exp_tri`) and `√r ≤ c r + 1/(4c)` (`tailtoTail_exp_sqrt_le`) give the `e^{√|a-b|}` moments; `α ρ² = ((W^d |1-t|)⁻¹)²` is `field_simp` (`hamp`).
- The hypothesis `g² ≤ 1-t` is used in `tailtoTail_theta_wt` (`tλ ≤ t + g²/2 ≤ t + (1-t)/2`, boundary `g² = 1-t` included) and, as `g² ≤ 1`, in `tailtoTail_ker_wt` (`1 + g²/2 ≤ 3/2`).
- Registry: the line for `STTailtoTail` is deleted from `owedProps` (`RBM3D/Test/Axioms.lean`); the pre-check above passes with the root import (4487 theorems, 0 axioms).

## (c) Verified Mathlib names (all by `#check` in `scratchpad/T2147/names.lean`, output in the tool log of this stage)
`Real.add_one_le_exp`, `Real.sqrt_le_left`, `Real.sq_sqrt`, `Real.sqrt_le_sqrt`, `Real.exp_add`, `Real.exp_le_exp`, `Real.exp_pos`, `Real.rpow_nonneg`, `piFinTwoEquiv`, `Fintype.sum_prod_type'`, `Fintype.sum_equiv`, `Equiv.subLeft`, `Finset.sum_mul_sum`, `Finset.sum_comm`, `Fin.prod_univ_two`, `inv_le_one_of_one_le₀`, `le_div_iff₀`, `norm_sum_le`, `norm_prod`, `Matrix.mul_apply`, `Matrix.one_apply`.
Verified absent: `grep -rn "sqrt_add_le" .lake/packages/mathlib/Mathlib` has 0 hits (no `√(x+y) ≤ √x + √y`); proved privately as `tailtoTail_sqrt_add_le`. `#check @Equiv.piFinTwo` gives `Unknown constant`; the name is `piFinTwoEquiv`.

## (d) Open issues and paper-delta candidates
- T2147a (statement): the paper (`3_5:2344-2362`) says "for some constant `D > 0`" and uses `≲`; the Lean theorem holds for every real `D` (no `D > 0`, no largeness) with the explicit `C = (3 e^{(4d+1)/4})²`; this is the merged pin `Step5Pins.lean:121`, not changed here.
- T2147b (proof route): the paper proves `(neiwuj)` from `(sum_res_Ndecay)`, `(prop:ThfadC)` and a continuum calculus fact (`3_5:2365`), details omitted. The Lean proof uses neither `prop:ThfadC` nor the continuum fact: a weighted resolvent bound `Σ_b Θ_t(a,b) e^{c|a-b|_∞} ≤ 2/(1-t)` with `c = 1/(4d+1)` (used in the regime `g² ≤ 1-t`, boundary included).
- Open: none for this ticket. S5-10 (`lem:pf_step5`) can use `stTailtoTail_holds` in place of the owed pin `STTailtoTail`.
