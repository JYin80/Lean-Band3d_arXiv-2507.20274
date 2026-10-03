Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 20:13:16 UTC 2026

Targets: `EKPropTInf d` (`EKPropT` with `zdistInf` in all three places) and `ekPropTInf_holds`. Mathematics: `Σ_c 𝒯_u(|a-c|_∞) 𝒯_t(|c-b|_∞) ≤ C_d/(1-u) · 𝒯_t(|a-b|_∞)`, `0 ≤ u ≤ t < 1`, (i) `g²/L² ≤ 1-t` or (ii) `1-u ≤ g²/L²`, `d = k+2 ≥ 3`. Lean side (read from files): `zdistInf` is `RBM.Gauss.zdistInf` (`Defs/Sizes.lean:115`); the facts `zdistInf_le_zdistD`, `zdistD_le_mul_zdistInf` are there (`:117,:122`).

### (i) Route and exponent table

Route A (ticket's first try: comparison + doubling `𝒯_t(d·r) ≥ c_d 𝒯_t(r)`) is **refuted**: the doubling lemma has no constant free of `L` (part 3 below: `g = 1, t = 0`, `ℓ_t = 1`; `min_{r ≤ L/2} 𝒯_t(3r)/𝒯_t(r)` is `2.7e-72` at `L = 1e5`, dominated by `e^{-(√3-1)√r}`). The ticket's own wording ("prove or refute it") is answered: false. Route B (direct, norm-generic, below) closes. The statement itself is not false: numerics (part 1, 2) show a bounded ratio.

Route B: the proof of merged `propT` (`Kernel/PropT.lean`, `Defs/Convolution.lean`) uses `ρ = zdistD` only through (a) the triangle inequality, (b) symmetry/translation `Σ_c F(a-c) = Σ_x F(x)`, (c) the range `ρ ≤ mL`, (d) the radial sum K2 `sum_radial_exp_le`. For `ρ = zdistInf`: (a) needs `zdistInf (x+y) ≤ zdistInf x + zdistInf y` (new; sup of the coordinatewise `zdist_add_le`, `Lattice.lean:38`); (b) unchanged; (c) `ρ ≤ L` (`zdist_le_L` coordinatewise, `RadialSum.lean:40`), i.e. `m = 1`; (d) from `ρ₁ ≤ d ρ`: `(ρ+1)^{-k} ≤ d^k (ρ₁+1)^{-k}` and `e^{-κ√(ρ/ℓ)} ≤ e^{-κ√(ρ₁/(dℓ))}`, so `Σ_x P(ρ)e^{-κ√(ρ/ℓ)} ≤ d^k · 2^d radC(κ)(dℓ)² = d^d 2^d radC(κ) ℓ²` by K2 at `ℓ' = dℓ ≥ 1`.

| quantity | value | constraint | slack |
|---|---|---|---|
| `d = k+2`, `k` (decay exponent of `P`) | 3, 1 | `k+1` (shell size of `K2`) `- k = 1` cancels exactly | borderline, absorbed by `e^{-κ√·}` as in `sum_radial_exp_le` |
| `κ₀ = 2-√2` (`sqrt_add_sqrt_sub_ge`, needs `ℓ_u ≤ ℓ_t`, triangle for `ρ`) | 0.5858 | `κ₀ > 0` | 0.586; `ℓ_u ≤ ℓ_t` from `ellT_mono` (`u ≤ t`), equality allowed |
| radial scale `ℓ' = dℓ_u` | `3 ℓ_u` | `ℓ' ≥ 1` (K2 hypothesis) | `ℓ_u ≥ 1` (`one_le_ellT`), so `ℓ' ≥ 3` |
| radial constant | `d^d = 27` factor on `convC` | `Σ_x ≤ d^d 2^d radC(κ)ℓ²` | part 4: true value 186.6 / 363.1 / 515.6 vs bound 1.2e8 / 2.0e9 / 3.6e10 (`ℓ = 1, 4, 17`) |
| range `ρ ≤ mL` (`zeroMode_le_of_ge_mul`, regime (i)) | `m = 1` (ℓ¹ proof: `m = d`) | `ρ ≤ L` | exact (`zdist ≤ L`); `zmC` shrinks: `2(2)^k = 4` vs 12 at `k=1` |
| `E_L(ρ) ≥ e^{-√(ρ/L)}` (regime (ii), `exp_neg_sqrt_ge` with `d := 1`) | `e^{-1}` (ℓ¹: `e^{-√d}`) | `ρ ≤ L` | `e^{-1}` vs `e^{-1.73}` |
| `A_uℓ_u² ≤ 1/(1-u)` (`inv_mul_ellT_sq_le`) | 1 | `ℓ_u² ≤ g²/(1-u)+1` (`ellT_sq_le`) | equality-type, constant 1 |
| regime split `s = g²/L²` | (i) `1-t ≥ s`; (ii) `1-u ≤ s` | `u ≤ t` | overlap only at `1-u = 1-t = s` (column F below), both proofs give the same bound |
| `C_∞` candidate | `d^d (constI k + constII k)` = 8.38e10 at `d=3` | `C ≥` sup of ratio `Σ(1-u)/𝒯_t` | observed sup ≤ 1.5e3 (part 1, 2): slack ≥ 5e7; free of `L, g, t, u` |
| doubling constant `c_d(L) = min_{r ≤ L/2} 𝒯_t(3r)/𝒯_t(r)` (`g=1, t=0`) | 8.2e-2 (`L=9`), 1.1e-23 (`L=1e4`), 2.7e-72 (`L=1e5`) | would need `c_d > 0` uniform in `L` | **fails** (Route A dead) |

Candidate `C_∞` is the argument's sufficient value (constants of merged `constI`, `constII` with `convC → d^d convC`, `zmC`, `exp √d` only decreasing); the prover recomputes it.

Findings for the dispatcher. (F1) `RBM3D.Defs.Sizes` (home of `zdistInf`, namespace `RBM.Gauss`) is **not** in the import closure of `RBM3D.Evolution.Pins` (script: transitive-import walk, output `Defs.Sizes False`, `Gauss.Model False`, `Defs.Convolution True`, `Defs.RadialSum True`, `Kernel.PropT True`, `Defs.Tail True`); the new file needs `import RBM3D.Defs.Sizes` (not the root `RBM3D`), and `zdistInf` is spelled `Gauss.zdistInf`. (F2) No public triangle inequality for `zdistInf` exists (only private `entryDom_zdistInf_neg/zero` in `Green/EntryDom.lean:105,110`): prove it privately. Paper-delta candidates: none (statement is the paper's `(TTT2)` with the paper's `L^∞` norm).

### (ii) Concrete nondegenerate instance and numerics

Commands: `cd scratchpad/T2075; python3 final.py; python3 part2.py; python3 inst.py` (numpy FFT, exact torus `Z_9^3`, `Z_17^3`, brute-force circular convolution; `𝒯` as in `Defs/Tail.lean`, `ℓ_t` as `ellT`).
Part 1: `max_b (Σ_c 𝒯_u𝒯_t)(1-u)/𝒯_t(|b|)`, `a = 0`, cell = `Rinf/R1` (`zdistInf` = new, `zdistD` = merged `EKPropT`), `-` = hypotheses fail.
```
part 1: max_b (sum_c T_u T_t)(1-u)/T_t(|b|), a=0, d=3; cell = Rinf/R1 (Rinf: zdistInf, R1: zdistD); '-' = hypotheses fail
cols: A(0,.5); B(.5,.9); C u=t=.3; D u=0,t=0; E u=0,1-t=s; F u=t,1-t=s; G 1-u=s/2,1-t=s/4; H(.995,.999)
L= 9 g=0.1  | 56.1/40.5 | 55.6/40.1 | 55.9/40.3 | 56.1/40.5 | 41.8/18.2 | 2.2/1.8 | 1.4/1.1 | 21.0/12.7
L= 9 g=1    | 26.8/17.5 | 21.0/12.7 | 26.1/19.1 | 28.4/20.5 | 21.2/9.3 | 2.2/1.8 | 1.4/1.1 | 1.2/0.9
L= 9 g=4    | 6.5/4.6 | - | 5.3/4.1 | 6.8/5.3 | 6.1/3.8 | 2.2/1.8 | 1.4/1.1 | 0.6/0.6
L= 9 g=20   | 0.9/0.8 | 0.7/0.7 | 0.8/0.8 | 0.9/0.8 | - | - | - | 0.6/0.6
L=17 g=0.1  | 162.3/98.6 | 160.7/97.6 | 161.6/98.2 | 162.3/98.6 | 99.2/31.9 | 2.6/2.0 | 1.5/1.2 | 60.5/30.6
L=17 g=1    | 74.6/39.7 | 60.5/30.6 | 77.6/48.5 | 82.0/49.8 | 50.2/16.1 | 2.6/2.0 | 1.5/1.2 | -
L=17 g=4    | 21.5/13.9 | 12.1/6.9 | 17.5/12.5 | 22.6/16.0 | 18.2/8.8 | 2.6/2.0 | 1.5/1.2 | 0.7/0.7
L=17 g=20   | 2.0/1.5 | 1.2/1.0 | 1.6/1.3 | 2.1/1.6 | - | - | 1.5/1.2 | 0.6/0.6
```
Parts 2-4 (`part2.py`):
```
part 2: saturation in L (g=1,u=0,t=0.5 and g=0.1,u=0,t=0.5): Rinf
  L=  9 Rinf=26.8 / 56.1
  L= 17 Rinf=74.6 / 162.3
  L= 33 Rinf=175.1 / 402.5
  L= 65 Rinf=324.5 / 807.2
  L=129 Rinf=451.2 / 1254.3
  L=257 Rinf=452.2 / 1452.4
part 3: doubling T_t(3r)/T_t(r) at g=1,t=0 (ell_t=1, 1-t>=g^2/L^2), worst r<=L/2 (r real, tailT def)
  L=     9 min ratio=8.223e-02
  L=    17 min ratio=4.271e-02
  L=   101 min ratio=1.859e-03
  L=  1001 min ratio=2.576e-08
  L= 10001 min ratio=1.099e-23
  L=100001 min ratio=2.705e-72
part 4: radial sum (d=3,L=17), S(l)=sum_x (rho+1)^-1 exp(-kap sqrt(rho/l)), rho=zdistInf, vs d^d 2^d radC(kap) l^2, kap=2-sqrt2
  l= 1.0 S=186.58 bound=1.232e+08
  l= 4.0 S=363.05 bound=1.971e+09
  l=17.0 S=515.55 bound=3.560e+10
part 5: merged l1 constants k=1: convC=1.8248e+07 zmC=12 constI=3.0840e+09 constII=2.0335e+07
  candidate C_inf = d^d (constI+constII) = 8.3816e+10 ; observed max Rinf (parts 1,2) <= 1500
```
Concrete instance (`inst.py`; `a = 0`, `b = (4,4,4)`, `L = 9`, `d = 3`; hypotheses `0 < g`, `0 ≤ u ≤ t < 1` and case (i)/(ii) flags checked in exact rationals; `C = 8.3816e10`):
```
d=3 L=9 a=0 b=(4, 4, 4) zdistInf(a-b)=4 zdistD=12
(i)                    g=1 u=1/2 t=9/10 g^2/L^2=0.01235 hyps=(True, True, (True, False)) LHS=2.47518e+00 C/(1-u)T_t=1.06448e+10 ratio LHS(1-u)/T_t=19.489
(ii)                   g=1 u=199/200 t=999/1000 g^2/L^2=0.01235 hyps=(True, True, (False, True)) LHS=1.86381e+02 C/(1-u)T_t=1.35255e+13 ratio LHS(1-u)/T_t=1.155
(i) bdry 1-t=g^2/L^2   g=1 u=0 t=80/81 g^2/L^2=0.01235 hyps=(True, True, (True, False)) LHS=3.19062e+00 C/(1-u)T_t=1.32830e+10 ratio LHS(1-u)/T_t=20.133
(ii) g>L               g=20 u=1/2 t=9/10 g^2/L^2=4.93827 hyps=(True, True, (False, True)) LHS=1.06395e-02 C/(1-u)T_t=1.22361e+09 ratio LHS(1-u)/T_t=0.729
```
Every hypothesis holds simultaneously at these data (no `N = 0`, window `|b|_∞ = 4 ≤ L/2`, `L^d = 729` points); boundaries covered: `u = t` (cols C, F), `1-t = g²/L²` exactly (col E, `t = 80/81`), `g > L` (`g = 20`), `u = 0` (cols A, D, E). Suggested compiled instance for stage 1b: `d = 3, L = 9, g = 1, u = 1/2, t = 9/10, a = 0, b = ![4,4,4]` (case (i)) and `u = 199/200, t = 999/1000` (case (ii)). No external hypothesis occurs (`EKPropTInf` has none), so no limit computation is needed.

Ratios grow with `L` at fixed `(g,u,t)` but saturate (part 2: `g=1`: 451 → 452 for `L = 129 → 257`; `g = 0.1`: 1254 → 1452), consistent with a bound free of `L`; the ℓ¹ ratio is smaller in every cell of part 1.

### Verdicts
* Target 1 `EKPropTInf`: PASS (definition; hypotheses satisfiable, instance above).
* Target 2 `ekPropTInf_holds`: PASS via Route B (direct, norm-generic port of `Kernel/PropT.lean` with `ρ = zdistInf`, K2 at `ℓ' = dℓ`). Route A: FAIL (doubling lemma false uniformly in `L`).

## (b) Script output — Sat Oct  3 20:28:22 UTC 2026

Branch `t/T2075`, commit `ae86da8`; the commit touches only `RBM3D/Evolution/PropTInf.lean` (662 lines); `RBM3D/Test/Axioms.lean` is untouched (no new premise: see the registry pre-check).

```
$ git diff --stat main...t/T2075
 RBM3D/Evolution/PropTInf.lean | 662 ++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 662 insertions(+)
$ lake build RBM3D.Evolution.PropTInf 2>&1 | tail -2
Build completed successfully (3189 jobs).
$ lake build 2>&1 | tail -1   # whole library in the worktree (the hub adds the root import at merge)
Build completed successfully (3790 jobs).
$ grep -n "sorry\|admit\|native_decide\|axiom" RBM3D/Evolution/PropTInf.lean ; echo rc=$?
rc=1
$ grep -n "^import" RBM3D/Evolution/PropTInf.lean
6:import RBM3D.Evolution.Pins
7:import RBM3D.Defs.Sizes
```

### Axioms
```
$ lake env lean scratchpad/T2075/ax.lean   # import RBM3D.Evolution.PropTInf; #print axioms RBM.ekPropTInf_holds
'RBM.ekPropTInf_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean scratchpad/T2075/PropTInfAx.lean   # copy of the file + #print axioms of the private instances
'RBM.ptiInst_i' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ptiInst_ii' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ptiInst_bdry_t' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ptiInst_bdry_ut' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ptiInst_bdry_u' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ptiInst_gL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ptiInst_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.pti_inst_dist' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ekPropTInf_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Registry pre-check (DECISIONS §20)
```
$ cat scratchpad/T2075/precheck.lean
import RBM3D
import RBM3D.Evolution.PropTInf

#assert_rbm_axioms
$ lake env lean scratchpad/T2075/precheck.lean > pc.out; echo exit=$?; head -1 pc.out; grep "^premises found" pc.out
exit=0
axiom audit: 2474 theorems, 1053 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 80 (borrowed 2, owed 65, structural 13).
$ same file without the second import (baseline), first line
axiom audit: 2473 theorems, 1052 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
```
The new module adds one theorem (`ekPropTInf_holds`) and one definition (`EKPropTInf`) to the scan and no premise: `EKPropTInf` is a conclusion, never a hypothesis, so no row of `Test/Axioms.lean` is needed.

### Target statements (extracted by script)
```
$ sed -n 522,530p RBM3D/Evolution/PropTInf.lean   # target 1
def EKPropTInf (d : ℕ) : Prop :=
  3 ≤ d →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) [NeZero L] (g u t : ℝ), 0 < g → 0 ≤ u → u ≤ t → t < 1 →
        (g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t ∨ 1 - u ≤ g ^ 2 / (L : ℝ) ^ 2) →
        ∀ a b : Zd d L,
          ∑ c : Zd d L, tailT d L g u (Gauss.zdistInf d L (a - c))
              * tailT d L g t (Gauss.zdistInf d L (c - b))
            ≤ C / (1 - u) * tailT d L g t (Gauss.zdistInf d L (a - b))
$ sed -n 534p RBM3D/Evolution/PropTInf.lean   # target 2 (statement line; proof follows)
theorem ekPropTInf_holds (d : ℕ) : EKPropTInf d := by
$ python3 cmp.py   # Pins.lean:142-149 (EKPropT) with EKPropT->EKPropTInf and "zdistD d L"->"Gauss.zdistInf d L", whitespace-normalised, against the new def
identical: True
```

### Compiled nonempty instances (private named theorems; every hypothesis discharged by `norm_num`; axioms above)
```
$ grep -n 'abbrev ptiB' RBM3D/Evolution/PropTInf.lean
580:private abbrev ptiB : Zd 3 5 := ![2, 2, 2]
$ awk '/(theorem|abbrev) pti_inst_dist /{f=1} f{print} f&&/^$/{exit}' RBM3D/Evolution/PropTInf.lean
private theorem pti_inst_dist :
    Gauss.zdistInf 3 5 (0 - ptiB) = 2 ∧ zdistD 3 5 (0 - ptiB) = 6 := by
  decide +kernel

$ awk '/(theorem|abbrev) ptiInst_i /{f=1} f{print} f&&/^$/{exit}' RBM3D/Evolution/PropTInf.lean
private theorem ptiInst_i : ∃ C : ℝ, 0 < C ∧
    ∑ c : Zd 3 5, tailT 3 5 (1 / 2) (1 / 2) (Gauss.zdistInf 3 5 (0 - c)) *
        tailT 3 5 (1 / 2) (9 / 10) (Gauss.zdistInf 3 5 (c - ptiB))
      ≤ C / (1 - 1 / 2) * tailT 3 5 (1 / 2) (9 / 10) (Gauss.zdistInf 3 5 (0 - ptiB)) := by
  obtain ⟨C, hC, H⟩ := ekPropTInf_holds 3 (by norm_num)
  exact ⟨C, hC, H 5 (1 / 2) (1 / 2) (9 / 10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Or.inl (by norm_num)) 0 ptiB⟩

$ awk '/(theorem|abbrev) ptiInst_uniform /{f=1} f{print} f&&/^$/{exit}' RBM3D/Evolution/PropTInf.lean
private theorem ptiInst_uniform : ∃ C : ℝ, 0 < C ∧
    (∑ c : Zd 3 5, tailT 3 5 (1 / 2) (1 / 2) (Gauss.zdistInf 3 5 (0 - c)) *
        tailT 3 5 (1 / 2) (9 / 10) (Gauss.zdistInf 3 5 (c - ptiB))
      ≤ C / (1 - 1 / 2) * tailT 3 5 (1 / 2) (9 / 10) (Gauss.zdistInf 3 5 (0 - ptiB))) ∧
    (∑ c : Zd 3 7, tailT 3 7 8 (1 / 50) (Gauss.zdistInf 3 7 (![1, 0, 0] - c)) *
        tailT 3 7 8 (1 / 2) (Gauss.zdistInf 3 7 (c - ![1, 2, 3]))
      ≤ C / (1 - 1 / 50) *
        tailT 3 7 8 (1 / 2) (Gauss.zdistInf 3 7 (![1, 0, 0] - ![1, 2, 3]))) := by
  obtain ⟨C, hC, H⟩ := ekPropTInf_holds 3 (by norm_num)
  exact ⟨C, hC,
    H 5 (1 / 2) (1 / 2) (9 / 10) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (Or.inl (by norm_num)) 0 ptiB,
    H 7 8 (1 / 50) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (Or.inr (by norm_num)) ![1, 0, 0] ![1, 2, 3]⟩

```

### Name clashes and ports
```
$ grep -rn "EKPropTInf\|ekPropTInf_holds" RBM3D RBM3D.lean | grep -v Evolution/PropTInf.lean | wc -l
0
$ grep -rln "pti_\|ptiConv\|ptiConst\|ptiZC\|ptiInst\|ptiB" RBM3D RBM3D.lean | grep -v Evolution/PropTInf.lean | wc -l
0
$ grep -rn "EKPropTInf\|ekPropTInf" /Users/junyin/Lean_proof/RBM1D /Users/junyin/Lean_proof/RBM2D --include="*.lean" | wc -l   # read-only
0
$ for f in Kernel/PropT Defs/Convolution Defs/RadialSum Defs/Sizes Evolution/Pins; do git log -1 --format="%h  RBM3D/$f.lean" -- RBM3D/$f.lean; done
c3f3d5d  RBM3D/Kernel/PropT.lean
fedc370  RBM3D/Defs/Convolution.lean
320f7b0  RBM3D/Defs/RadialSum.lean
0a873f1  RBM3D/Defs/Sizes.lean
d9de66f  RBM3D/Evolution/Pins.lean
$ grep -n "theorem propT_ii\|theorem propT_i \|theorem tailT_le_decay" RBM3D/Kernel/PropT.lean; grep -n "theorem conv_term_le\|theorem sum_conv_le" RBM3D/Defs/Convolution.lean
126:theorem propT_ii [NeZero L] (hg : 0 < g) (hut : u ≤ t) (
307:theorem tailT_le_decay [NeZero L] {s : ℝ} (hs : s < 1) (
333:theorem propT_i [NeZero L] (hg : 0 < g) (hut : u ≤ t) (h
153:theorem conv_term_le (d k : ℕ) {ℓ₁ ℓ₂ : ℝ} (hℓ₁ : 0 < ℓ₁
225:theorem sum_conv_le (k : ℕ) {ℓ₁ ℓ₂ : ℝ} (hℓ₁ : 1 ≤ ℓ₁) (
$ python3 const.py   # d = 3 (k = 1): ptiConvC = 2^(k+1) d^d 2^(k+2) radC(kappa0), ptiZC = 2*2^k, ptiConstI, ptiConstII as defined in the file
d=3: ptiConvC=4.9270e+08 ptiZC=4 ptiConstI=1.2318e+10 ptiConstII=5.1980e+08 C=ptiConstI+ptiConstII=1.2837e+10
$ grep -n "def zdistInf\|theorem zdistD_le_mul_zdistInf" RBM3D/Defs/Sizes.lean; grep -n "theorem zdist_le_L" RBM3D/Defs/RadialSum.lean   # (a)'s Lean references
115:def zdistInf (d L : ℕ) (x : Zd d L) : ℕ := Finset.univ.sup fun i => zdist L (x i)
122:theorem zdistD_le_mul_zdistInf (d L : ℕ) (x : Zd d L) : zdistD d L x ≤ d * zdistInf d 
40:theorem zdist_le_L (u : ZMod L) : zdist L u ≤ L := by
```

Narrative (stage 1b, `claude-sonnet-5-5`).
* Route. Route A (comparison + doubling) is not used: section (a) part 3 (script output there) gives `min_{r ≤ L/2} 𝒯_t(3r)/𝒯_t(r) = 2.7e-72` at `L = 1e5`, so no doubling constant is free of `L`; I did not re-run that script. Route B (direct) is a re-proof of `Kernel/PropT.lean` with `ρ = Gauss.zdistInf`: `PropT.lean:126` `propT_ii`, `:307` `tailT_le_decay`, `:333` `propT_i`, and `Convolution.lean:153` `conv_term_le`, `:225` `sum_conv_le`, all at commit `c3f3d5d` / `fedc370` (merged RBM3D files; no RBM1D/RBM2D file was read except by the name grep above).
* Changes against the merged proofs (all private, prefix `pti`): triangle inequality `pti_zdistInf_add_le` (`PropTInf.lean:43`, coordinatewise `zdist_add_le`; F2 of (a)); range `pti_zdistInf_le_L` (`:53`), used as `m = 1` in `zeroMode_le_of_ge_mul` and `d = 1` in `exp_neg_sqrt_ge`; radial sum `pti_sum_radial` (`:88`) from `pti_term_le` (`:59`, `ρ₁ ≤ dρ`: `P(ρ)e^{-κ√(ρ/ℓ)} ≤ d^k P(ρ₁)e^{-κ√(ρ₁/(dℓ))}`) and the merged `sum_radial_exp_le` at scale `dℓ`; `pti_conv_term_le` (`:114`), `pti_sum_conv_le` (`:187`); regimes `pti_ii` (`:229`), `pti_i` (`:438`) with `pti_tailT_le_decay` (`:411`).
* Constant: `C = ptiConstI k + ptiConstII k`, `d = k+2`, depends on `d` only; `d = 3`: `C = 1.2837e10` (`const.py` above). Section (a) observed sup of the ratio `≤ 1.5e3` (parts 1-2), so the proved `C` is a valid but loose bound by a factor about `8.6e6`.
* Statement. `EKPropTInf` is `EKPropT` with `Gauss.zdistInf` in the three places (script `cmp.py`: identical). Paper: `(TTT2)` is `3_5_Loop_Hierarchy.tex:338`, `|·|` is the `L^∞` metric (`1_2_Intro_model_result.tex:274`). The paper's (i) `1-u ≥ 1-t ≥ g²/L²` and (ii) `1-t ≤ 1-u ≤ g²/L²` equal the Lean disjunction `g²/L² ≤ 1-t ∨ 1-u ≤ g²/L²` under `u ≤ t`. Proof sketch of the paper: `A_deterministic_estimates.tex:230-258`.
* DECISIONS §29 boundary checks, each a compiled instance at `d = 3`, `L = 5`, `g = 1/2` unless stated (`b = (2,2,2)`, `|b|_∞ = 2`, `|b|_{ℓ¹} = 6`, `pti_inst_dist`): case (i) `u = 1/2, t = 9/10` (`ptiInst_i`); case (ii) `u = 199/200, t = 999/1000` (`ptiInst_ii`); `1-t = g²/L²` exactly with `u = 0` (`ptiInst_bdry_t`); `u = t` with `1-t = g²/L²` (`ptiInst_bdry_ut`); `1-u = g²/L²` exactly (`ptiInst_bdry_u`); `g = 10 > L = 5`, `u = 0` (`ptiInst_gL`); `C` free of `L, g, t`: it is quantified before them in `EKPropTInf`, and `ptiInst_uniform` uses one `C` at `L = 5` (case (i)) and `L = 7`, `g = 8` (case (ii)). `0 ≤ u`, `t < 1` are hypotheses of the statement; `L`, `W` play no role (no `W`).
* No hypothesis added, nothing weakened, no pinned signature changed; `hd : 3 ≤ d` is used only to write `d = k + 2` (the merged proof does too). The file imports `RBM3D.Defs.Sizes` besides `RBM3D.Evolution.Pins` (F1 of (a)). Section (a) needs no correction: its Lean references are confirmed by the grep above (`Sizes.lean:115,122`, `RadialSum.lean:40`).

## (c) Verified names (`#check` in `scratchpad/T2075/names.lean`, output in the tool log)
Mathlib: `Finset.sup_le`, `Finset.le_sup`, `Nat.add_le_add`, `pow_le_pow_left₀`, `mul_pow`, `div_le_div_iff₀`, `inv_eq_one_div`, `div_eq_mul_inv`, `Real.sqrt_le_sqrt`, `Real.exp_le_exp`, `Real.exp_pos`, `Real.exp_add`, `Real.sqrt_one`, `Finset.sum_le_sum`, `Finset.mul_sum`, `Finset.sum_add_distrib`, `Fintype.sum_equiv`, `Equiv.subLeft`, `Equiv.subRight`, `sub_add_sub_cancel`, `mul_le_mul`, `mul_le_mul_of_nonneg_left`, `mul_le_mul_of_nonneg_right`, `div_le_div_of_nonneg_right`, `Nat.cast_nonneg`, `Nat.cast_one` (all exist; signatures as printed).
Project (used unchanged): `tailT_natCast`, `ellT_mono`, `inv_mul_ellT_sq_le`, `exp_neg_sqrt_ge`, `zeroMode_le_of_ge_mul`, `sum_one_torus`, `sqrt_add_sqrt_sub_ge`, `powW_le_of_le_two_mul`, `sum_radial_exp_le`, `zdist_add_le`, `zdist_le_L`, `Gauss.zdistD_le_mul_zdistInf`, `tailT_nonneg`, `one_le_ellT`, `radC_pos`, `κ₀_pos`.
Names verified absent: none searched for.

## (d) Open issues and paper-delta candidates
* The ticket's import line (`Pins` and Mathlib) is incomplete: `Gauss.zdistInf` lives in `RBM3D.Defs.Sizes`, which `Pins` does not import (F1 of (a)); the file imports it directly, not the root `RBM3D`.
* The private instances state `∃ C` (as `ekInstPropT` in `Pins.lean` does); the numeric `C` for `d = 3` is in `const.py`.
* Paper-delta candidates: none. The merged `propT` / `EKPropT` are for the `ℓ¹` distance `zdistD`; the paper's `|·|` is `L^∞` (`1_2_Intro_model_result.tex:274`), so `EKPropTInf` is the paper's statement, not a deviation from it.
* `Test/Axioms.lean`: no row needed (pre-check exit 0, no new premise). Root import `RBM3D.Evolution.PropTInf` is for the hub at merge.
