Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 04:41:13 UTC 2026

All eight targets are the statements of `docs/tickets/checks/T2324-check.lean` section 3; below only what (i)-(ii) need. Conventions: `N = L^d`, `v_i = g*lambda_i(Psi)`, `|lambda_i| <= 2d`, `w = E+m`, `f_i = (v_i - w)^-1`, `K_ab = |M_ab|^2`, `r = zdistD`.

### (i) Exponent / constant table

| quantity | value | constraint | slack |
|---|---|---|---|
| T1 variance: `Var(v) = N^-1 g^2 tr Psi^2 - (N^-1 g tr Psi)^2` | `2 d g^2` | `tr Psi = 0`, `tr Psi^2 = sum_a deg(a) = 2dN` needs `3 <= L` (`card_adj`), `0<d` | exact (script asserts tr Psi = 0, tr Psi^2 = 2dN for L=4,6,8) |
| T1 Ward: `N^-1 sum |f_i|^2` | `1` | `Im(self_m)`, `Im m > 0` (in `BAReal`) | exact; `1-|m|^2 = Var(f) = (1/2)N^-2 sum_ij |f_i-f_j|^2` |
| T1 `R = 2dg + |E+m|` | `|v_i - w| <= R` | `|v_i|<=2dg` | `1-|m|^2 >= 2dg^2/R^4`: ratio over the grid: min 5.58 (L=4,g=.1,E=0), max 850; instance 224 |
| T4 `R <= 4 d Lam + 3` | `2dg <= 2d Lam`; `|E| <= 2+2dg` (`baSelf_none_of_gt`, contrapositive of `BAReal`), `|m|<=1` | `g <= Lam` | `R<=2dLam+2dLam+2+1`; exact algebra |
| T4 `c` | `kap^2/(4(4d Lam+3)^8)` (d=3,Lam=2,kap=.35: `1.08e-13`) | `c` depends on `(d,Lam,kap)` only, quantified before `L`, `g`, `E`, `m` | from `BAK_adj_sum_ge`: `sum_{b~0}K_0b >= kap^2 d g^2/(2R^8)`; /(2d) by T3: `kap^2 g^2/(4R^8)`; actual `rawK/g^2 >= 8e-4` in grid vs `c<=1.1e-13`: slack >= 2.7e9 (D column; c is a conservative constant, not a witness) |
| T3 neighbour count | `2d` distinct neighbours `±e_i` | `3 <= L`, `0<d` (divide by `2d`) | exact; T2 (perm, any `g,z,m`) + `BAK_zero_neg` give equality (script `eq` <= 3e-16) |
| T2 `Mres` conjugation | `Ring.inverse(P H P^T - ..) = P Ring.inverse(..) P^T` | `zdistD(x∘s) = zdistD(x)` (sum over coordinates reindexed) | no hypothesis on `g,z,m`; script `P` <= 5e-15 |
| T5 sine part | `sum_a K_0a sin(theta.a) = 0` | `(-a)_j.val = L - a_j.val` (`a_j != 0`), `a -> -a` bijection, `BAK_zero_neg`; holds for every `L>=1` (`NeZero`) | exact; script `S5` <= 1.2e-15 |
| T6 gap constant `c6` | `4 c / pi^2` (d=3,Lam=2,kap=.35: `4.4e-14`) | `1-cos x >= 2x^2/pi^2` on `[-pi,pi]`, `x=2 pi zdist(k_i)/L`, `zdist <= L/2`; `1-Khat = sum_a K_0a(1-cos) >= sum_{i,±} K_{0,±e_i}(1-cos theta_i)`; `cos(2 pi k_i (L-1)/L) = cos(2 pi k_i/L)` | `3<=L`; actual `gap >= 5.0e-4` in grid vs `c6 = 4.4e-14` |
| T7 laziness | `1+Khat >= 2 K_00 >= 2 kap^2` | `K>=0`, `sum_a K_0a=1` (`BAK_row_sum`), `K_00>=kap^2` (`BAK_diag_bounds`); no `g,L` hypothesis | script `lazy` >= 1.0043 (kap up to .97), i.e. `1+Khat >= 2kap^2 *1.0043` |
| T8 `mu = BAct_rate d Lam kap` | `min(log(1+kap/(4d Lam)), kap/2)`; d=3,Lam=2,kap=.35: `0.01448 > 0` | `0<=mu<=BAct_rate`, `2<=d` (inherited from `BAK_exp_moment_le`), `3<=L` | `r^2 <= (2/mu^2)e^(mu r)`; `a=0` term has `r=0`; `sum_(a!=0) K_0a e^(mu r) <= A g^2 S` (diagonal `|m|^2` cancels exactly) |
| T8 `C = 2 A S / mu^2` | `A=4(BAct_C/mu)^2 = 2.15e11`, `S=expC 1 mu = 1.40e11`, `BAct_C=16d^2/kap^3=3359` (d=3,Lam=2,kap=.35): `C = 2.9e26` | `C(d,Lam,kap)` before `L` | actual `sm = sum K r^2/g^2 <= 26.8` in grid; slack factor 1e25; `C` is a constant, no witness depends on it |
| quantifier order (T4,T6,T8) | `forall d>0, Lam, kap>0, exists c>0, forall L>=3, g, E, m` | `c` independent of `L, g, E, m` | consistent with all constants above (functions of `d, Lam, kap` only) |
| external hypotheses | none (no `Prop` assumed; all statements unconditional); paper-delta D614 (large-`g` non-degeneracy, the paper has only `(Mbound_AO)` for `g<(2C)^-1`, `7_8:1891`) | | no concrete-limit computation needed |

### (ii) Concrete nondegenerate instance

Data: `d=3`, `L=4` (`N=64`), `g=1`, `E=0.7`, `Lam=2`, `m` the numerical solution of `(self_m)` (`kap = Im m`). Hypotheses of every target (`3<=L`, `0<d`, `2<=d`, `0<g<=Lam`, `0<kap`, `BAReal`) hold. The compiled Lean instance uses `P : FlowPt 4 10` of `KKernelInst` (`BA/MFixedPoint.lean:56`, `P.real : BAReal 3 4 P.g0 P.m0.im P.E P.m0`, `0 < P.g0 <= 10`), an existential witness (`Exists.some`), so its numbers are not computable; the script solves the same equation at `g=1, E=0.7`.

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2324/inst.py` (numpy 2.0.2, `/usr/bin/python3`; script builds `Psi`, `M=(g Psi-(E+m))^-1`, `K=|M|^2`)
```
d,L,N,g,E = 3 4 64 1.0 0.7   Lambda= 2.0   3<=L: True 0<d: True 0<g<=Lam: True
m = (-0.2993434383466903+0.4489890784104169j)  residual of (self_m): 3.885780586188048e-16  Im m =kappa = 0.4489890784104169
|m|^2 = 0.2911976866130543   1-|m|^2 = 0.7088023133869457   R=2dg+|E+m| = 6.601761475110934   bound 2dg^2/R^4 = 0.003158725848676756
sum_b K_0b = 1.0000000000000002   K_00 = 0.2911976866130546   kappa^2 = 0.2015911925318355   2kappa^2 = 0.403182385063671
K_{0,e_i} = [np.float64(0.01284437180815257), np.float64(0.012844371808152724), np.float64(0.012844371808152661)]  c g^2 (c=kap^2/(4(4d*Lam+3)^8)) = 1.784437943739971e-13
Khat(k=0) = 1.0000000000000002   max_k Khat = 1.0000000000000002  min_k Khat = -0.008165542987560892
swap(0,1) on a=(1,0,0),b=(0,1,0): |M[a∘s,b∘s]-M[a,b]| = 1.6184142622847344e-16
```
Targets at this instance: T1 `0.7088 >= 0.00316`; T2 swap error `1.6e-16`; T3 `K_{0,e_i}` all `0.012844`; T4 `0.012844 >= 1.8e-13`; T5/T6 `Khat` real, `Khat(0)=1`, `min Khat = -0.0082 < 1`; T7 `1+min Khat = 0.9918 >= 2kap^2 = 0.4032`; T8 see grid.

Grid command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2324/pf.py` (d=3, `L in {4,6,8}`, `g in {0.1,0.5,1,2}`, `E in {0,0.7}`, `m` by `fsolve`, `Im m>0`, `Lam=2`). columns: V=(1-|m|^2)/(2dg^2/R^4) [>=1]; P=max|M_{sa,sb}-M_ab| over all 6 coordinate perms; D=min_{i,±}K_{0,±e_i}/(c g^2), c=kap^2/(4(4d*Lam+3)^8), rawK/g2=min K_{0,±e_i}/g^2; eq=max|K_{0,±e_i}-mean_nbr K_0b|; gap=min_{k!=0}(1-Khat)/(g^2|theta|^2); lazy=min_k(1+Khat)/(2kap^2); S5=max|Im sum K_0a e^{i theta.a}|; sm=sum K_0a zdistD(a)^2/g^2; ward=|sum_b K_0b - 1|
```
L=4 g=0.1 E=0.0 kap=0.9722 | V=5.5801 | P=7.8e-16 | D=9.97e+11 rawK/g2=0.8340 | eq=5.2e-18 | gap=0.3410 | lazy=1.0046 | S5=1.6e-17 | sm=7.188 | ward=7.8e-16
L=4 g=0.1 E=0.7 kap=0.9137 | V=5.8431 | P=1.3e-15 | D=1.14e+12 rawK/g2=0.8433 | eq=8.7e-18 | gap=0.3449 | lazy=1.1367 | S5=2.3e-17 | sm=7.319 | ward=1.1e-16
L=4 g=0.5 E=0.0 kap=0.6988 | V=63.8499 | P=6.7e-16 | D=2.69e+11 rawK/g2=0.1164 | eq=2.4e-17 | gap=0.0681 | lazy=1.3733 | S5=1.0e-16 | sm=20.509 | ward=0.0e+00
L=4 g=0.5 E=0.7 kap=0.6193 | V=82.2252 | P=9.3e-16 | D=4.19e+11 rawK/g2=0.1423 | eq=7.6e-17 | gap=0.0893 | lazy=1.6037 | S5=2.5e-16 | sm=24.857 | ward=4.4e-16
L=4 g=1.0 E=0.0 kap=0.5959 | V=203.4416 | P=8.6e-16 | D=3.68e+10 rawK/g2=0.0116 | eq=4.2e-17 | gap=0.0075 | lazy=1.5594 | S5=2.3e-16 | sm=11.511 | ward=0.0e+00
L=4 g=1.0 E=0.7 kap=0.4490 | V=224.3950 | P=1.1e-15 | D=7.20e+10 rawK/g2=0.0128 | eq=8.2e-17 | gap=0.0085 | lazy=2.4600 | S5=3.2e-16 | sm=13.329 | ward=2.2e-16
L=4 g=2.0 E=0.0 kap=0.5681 | V=704.0477 | P=1.0e-15 | D=2.79e+09 rawK/g2=0.0008 | eq=1.9e-17 | gap=0.0005 | lazy=1.5928 | S5=1.9e-16 | sm=3.515 | ward=2.2e-16
L=4 g=2.0 E=0.7 kap=0.4385 | V=720.7306 | P=1.4e-15 | D=4.79e+09 rawK/g2=0.0008 | eq=5.1e-17 | gap=0.0005 | lazy=2.5945 | S5=3.6e-16 | sm=3.643 | ward=8.9e-16
L=6 g=0.1 E=0.0 kap=0.9720 | V=5.6174 | P=1.7e-15 | D=1.01e+12 rawK/g2=0.8461 | eq=6.9e-18 | gap=0.3453 | lazy=1.0043 | S5=1.8e-17 | sm=7.057 | ward=4.4e-16
L=6 g=0.1 E=0.7 kap=0.9136 | V=5.8722 | P=1.8e-15 | D=1.16e+12 rawK/g2=0.8542 | eq=2.1e-17 | gap=0.3486 | lazy=1.1362 | S5=5.3e-17 | sm=7.155 | ward=6.7e-16
L=6 g=0.5 E=0.0 kap=0.6590 | V=67.6052 | P=1.4e-15 | D=3.70e+11 rawK/g2=0.1423 | eq=9.0e-17 | gap=0.1003 | lazy=1.4478 | S5=2.4e-16 | sm=22.467 | ward=6.7e-16
L=6 g=0.5 E=0.7 kap=0.6519 | V=80.1991 | P=1.3e-15 | D=3.55e+11 rawK/g2=0.1335 | eq=8.3e-17 | gap=0.0951 | lazy=1.5248 | S5=2.5e-16 | sm=22.423 | ward=1.1e-16
L=6 g=1.0 E=0.0 kap=0.4189 | V=233.2860 | P=1.7e-15 | D=1.22e+11 rawK/g2=0.0189 | eq=4.9e-17 | gap=0.0217 | lazy=2.7586 | S5=3.2e-16 | sm=18.177 | ward=4.4e-16
L=6 g=1.0 E=0.7 kap=0.4194 | V=301.4719 | P=3.0e-15 | D=1.48e+11 rawK/g2=0.0230 | eq=9.4e-17 | gap=0.0313 | lazy=2.7022 | S5=4.3e-16 | sm=19.986 | ward=1.3e-15
L=6 g=2.0 E=0.0 kap=0.3518 | V=849.8245 | P=1.5e-15 | D=1.22e+10 rawK/g2=0.0013 | eq=4.3e-17 | gap=0.0017 | lazy=3.9502 | S5=1.1e-15 | sm=5.716 | ward=5.6e-16
6 2.0 0.7 no Im m>0 solution found
L=8 g=0.1 E=0.0 kap=0.9720 | V=5.6171 | P=1.9e-15 | D=1.01e+12 rawK/g2=0.8460 | eq=2.3e-17 | gap=0.3452 | lazy=1.0043 | S5=5.7e-17 | sm=7.055 | ward=4.4e-16
L=8 g=0.1 E=0.7 kap=0.9136 | V=5.8722 | P=2.8e-15 | D=1.16e+12 rawK/g2=0.8541 | eq=1.2e-17 | gap=0.3486 | lazy=1.1362 | S5=2.8e-17 | sm=7.152 | ward=1.1e-16
L=8 g=0.5 E=0.0 kap=0.6693 | V=66.7148 | P=2.2e-15 | D=3.42e+11 rawK/g2=0.1355 | eq=1.7e-16 | gap=0.0911 | lazy=1.4718 | S5=3.9e-16 | sm=22.944 | ward=3.3e-16
L=8 g=0.5 E=0.7 kap=0.6446 | V=80.9030 | P=2.4e-15 | D=3.70e+11 rawK/g2=0.1361 | eq=1.5e-16 | gap=0.0945 | lazy=1.5649 | S5=5.2e-16 | sm=23.685 | ward=8.9e-16
L=8 g=1.0 E=0.0 kap=0.4665 | V=228.0088 | P=2.0e-15 | D=8.83e+10 rawK/g2=0.0170 | eq=6.2e-17 | gap=0.0202 | lazy=2.5096 | S5=4.3e-16 | sm=25.899 | ward=4.4e-16
L=8 g=1.0 E=0.7 kap=0.3792 | V=288.8318 | P=4.6e-15 | D=1.50e+11 rawK/g2=0.0191 | eq=2.6e-16 | gap=0.0291 | lazy=3.5176 | S5=1.2e-15 | sm=26.766 | ward=2.2e-16
L=8 g=2.0 E=0.0 kap=0.3892 | V=832.9645 | P=3.2e-15 | D=9.32e+09 rawK/g2=0.0012 | eq=5.6e-17 | gap=0.0020 | lazy=3.3571 | S5=6.7e-16 | sm=10.693 | ward=4.4e-16
8 2.0 0.7 no Im m>0 solution found
--- constants (d=3, Lambda=2, kappa=0.35 <= every kappa above): 
BAct_C=3359 mu=BAct_rate=0.01448 A=2.153e+11 S=expC=1.398e+11
R<=4d*Lam+3=27.0  c4=kap^2/(4R^8)=1.084e-13  c6=4c4/pi^2=4.395e-14  C8=2AS/mu^2=2.872e+26  lazy 2kap^2=0.24499999999999997
```
The two lines `6 2.0 0.7 no Im m>0 solution found` and `8 2.0 0.7 ...` mean the numerical solver found no `m` at those two points; `BAReal` is not asserted there and no target is evaluated; every printed row satisfies all inequalities (V >= 5.58 >= 1; D >= 2.7e9 >= 1; gap >= 5e-4 > c6; lazy >= 1.0043 >= 1; sm <= 26.8 << C).

### Verdicts

- T1 `BAvar_lower`: PASS. T2 `BAMB_perm`: PASS. T3 `BAK_dir_eq`: PASS. T4 `BAK_dir_ge`: PASS (c = kap^2/(4(4d Lam+3)^8)).
- T5 `BAKhat_eq`: PASS. T6 `BAK_gap`: PASS. T7 `BAK_lazy`: PASS. T8 `BAK_second_moment`: PASS (`2<=d` as stated).
- Observation: the ticket's "(V) ratio >= 1.01 in T2317's table" is not reproduced as a number here (ratio in this grid is >= 5.58); the inequality direction holds in every row.

## (a′) Preflight corrections — Thu Oct  8 06:27:44 UTC 2026

- (a)(ii) says `P : FlowPt 4 10` is "of `KKernelInst` (`BA/MFixedPoint.lean:56`)". By `grep`, `P` is `RBM.BA.MFixedPointInst.P` at `RBM3D/BA/MFixedPoint.lean:893`, `structure FlowPt` is at `:877` (`:56` lies in `BAimInv_diag`); `KKernelInst` (`BA/KKernel.lean:389`) opens `MFixedPointInst` and reuses `P`. `KSymbolInst` does the same. The correction changes no verdict, number or hypothesis of (a).

## (b) Script output (stage 1b; the commit is `cf189e6`; every output below was re-run unchanged on the rerun, see the block "Rerun")

Commit on `t/T2324`: `cf189e6`; only file `RBM3D/BA/KSymbol.lean`; line 1 of the report is the prover id.

### Build of the module, full build, registry pre-check
```
$ lake build RBM3D.BA.KSymbol > out 2>&1; echo $?   -> 0   (last line of out:)
Build completed successfully (3739 jobs).
```
```
$ lake build   (whole library in the worktree; `RBM3D.lean` has no `import RBM3D.BA.KSymbol` before the merge)   -> exit 0, last line:
Build completed successfully (4129 jobs).
```
```
$ printf "import RBM3D\nimport RBM3D.BA.KSymbol\n#assert_rbm_axioms\n" > registry.lean; lake env lean registry.lean   -> exit 0
axiom audit: 9115 theorems, 2948 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
```

### `#print axioms` (targets; the other new public declarations are in the count line)
```
'RBM.BA.BAvar_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMB_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAK_dir_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAK_dir_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAKhat_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAK_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAK_lazy' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAK_second_moment' depends on axioms: [propext, Classical.choice, Quot.sound]
lines with exactly [propext, Classical.choice, Quot.sound]: 21 of 21 (8 targets, BAK_perm, definitions BAKhat and BAthetaSq, 10 KSymbolInst declarations)
```
`grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/BA/KSymbol.lean` -> no match

### Target statements (extracted by script from the file: text between `theorem <name> :` and `:= by`)
```lean
theorem BAvar_lower : ∀ (d L : ℕ) [NeZero L], 3 ≤ L → 0 < d → ∀ (g κ E : ℝ) (m : ℂ), 0 < g → 0 < κ → BAReal d L g κ E m →
    2 * (d : ℝ) * g ^ 2 / (2 * (d : ℝ) * g + ‖(E : ℂ) + m‖) ^ 4 ≤ 1 - ‖m‖ ^ 2
theorem BAMB_perm : ∀ (d L : ℕ) [NeZero L] (σ : Equiv.Perm (Fin d)) (g : ℝ) (z m : ℂ) (a b : Zd d L),
    BAMB d L g z m (fun j => a (σ j)) (fun j => b (σ j)) = BAMB d L g z m a b
theorem BAK_dir_eq : ∀ (d L : ℕ) [NeZero L], 3 ≤ L → 0 < d → ∀ (g E : ℝ) (m : ℂ) (i : Fin d) (s : Bool),
    BAK d L g E m 0 (unitVec d L (i, s)) =
      (2 * (d : ℝ))⁻¹ * ∑ b ∈ Finset.univ.filter (fun b : Zd d L => Adj d L 0 b), BAK d L g E m 0 b
theorem BAK_dir_ge : ∀ d : ℕ, 0 < d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ c : ℝ, 0 < c ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∀ (i : Fin d) (s : Bool), c * g ^ 2 ≤ BAK d L g E m 0 (unitVec d L (i, s))
theorem BAKhat_eq : ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (k : Zd d L),
    (∑ a : Zd d L, (BAK d L g E m 0 a : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I / L * ∑ j, ((k j).val : ℂ) * ((a j).val : ℂ))) =
      (BAKhat d L g E m k : ℂ)
theorem BAK_gap : ∀ d : ℕ, 0 < d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ c : ℝ, 0 < c ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∀ k : Zd d L, c * g ^ 2 * BAthetaSq d L k ≤ 1 - BAKhat d L g E m k
theorem BAK_lazy : ∀ (d L : ℕ) [NeZero L] (g κ E : ℝ) (m : ℂ), 0 < κ → BAReal d L g κ E m →
    ∀ k : Zd d L, 2 * κ ^ 2 ≤ 1 + BAKhat d L g E m k
theorem BAK_second_moment : ∀ d : ℕ, 2 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∑ a : Zd d L, BAK d L g E m 0 a * (zdistD d L a : ℝ) ^ 2 ≤ C * g ^ 2
```
Definitions (verbatim in the file, lines 478, 483): `BAKhat`, `BAthetaSq`.

### Check-file equality (acceptance (a), (b)); scripts `eq.py`, `scratch_eq.lean` in the scratchpad
```
(a) section-2 definitions equal (whitespace-normalized): True 466
statement BAvar_lower equal: True
statement BAMB_perm equal: True
statement BAK_dir_eq equal: True
statement BAK_dir_ge equal: True
statement BAKhat_eq equal: True
statement BAK_gap equal: True
statement BAK_lazy equal: True
statement BAK_second_moment equal: True
$ lake env lean scratch_eq.lean   (check imports + import RBM3D.BA.KSymbol, section-2 defs removed, 8 lines `example : T2324_<n> := @RBM.BA.<n>`) -> exit 0, "error" lines: 0
```

### Compiled nonempty instances (`RBM.BA.KSymbolInst`, data `P : FlowPt 4 10` of `MFixedPointInst`, `d = 3`, `L = 4`; statement text up to `:=`, whitespace-normalized)
```lean
theorem inst_var_lower : 2 * (3 : ℝ) * P.g0 ^ 2 / (2 * (3 : ℝ) * P.g0 + ‖(P.E : ℂ) + P.m0‖) ^ 4 ≤ 1 - ‖P.m0‖ ^ 2
theorem inst_perm : BAMB 3 4 P.g0 (P.E : ℂ) P.m0 (fun j => (![1, 0, 0] : Zd 3 4) (Equiv.swap (0 : Fin 3) 1 j)) (fun j => (![0, 1, 0] : Zd 3 4) (Equiv.swap (0 : Fin 3) 1 j)) = BAMB 3 4 P.g0 (P.E : ℂ) P.m0 ![1, 0, 0] ![0, 1, 0]
theorem inst_dir_eq : BAK 3 4 P.g0 P.E P.m0 0 (unitVec 3 4 (0, true)) = (2 * (3 : ℝ))⁻¹ * ∑ b ∈ Finset.univ.filter (fun b : Zd 3 4 => Adj 3 4 0 b), BAK 3 4 P.g0 P.E P.m0 0 b
theorem inst_dir_ge : ∃ c : ℝ, 0 < c ∧ c * P.g0 ^ 2 ≤ BAK 3 4 P.g0 P.E P.m0 0 (unitVec 3 4 (1, false))
theorem inst_Khat_eq : (∑ a : Zd 3 4, (BAK 3 4 P.g0 P.E P.m0 0 a : ℂ) * Complex.exp (2 * Real.pi * Complex.I / (4 : ℕ) * ∑ j, (((![1, 0, 0] : Zd 3 4) j).val : ℂ) * ((a j).val : ℂ))) = (BAKhat 3 4 P.g0 P.E P.m0 ![1, 0, 0] : ℂ)
theorem inst_thetaSq_pos : 0 < BAthetaSq 3 4 ![1, 0, 0]
theorem inst_gap : ∃ c : ℝ, 0 < c ∧ c * P.g0 ^ 2 * BAthetaSq 3 4 ![1, 0, 0] ≤ 1 - BAKhat 3 4 P.g0 P.E P.m0 ![1, 0, 0]
theorem inst_lazy : 2 * P.m0.im ^ 2 ≤ 1 + BAKhat 3 4 P.g0 P.E P.m0 ![1, 0, 0]
theorem inst_second_moment : ∃ C : ℝ, 0 < C ∧ ∑ a : Zd 3 4, BAK 3 4 P.g0 P.E P.m0 0 a * (zdistD 3 4 a : ℝ) ^ 2 ≤ C * P.g0 ^ 2
theorem inst_Khat_zero : BAKhat 3 4 P.g0 P.E P.m0 0 = 1
```
All hypotheses are discharged at the data (`3 ≤ 4`, `0 < 3`, `0 < P.g0 ≤ 10`, `0 < 10`, `P.real : BAReal 3 4 P.g0 P.m0.im P.E P.m0`); no hypothesis is left open. `inst_perm` is at `Equiv.swap 0 1`, `inst_thetaSq_pos` shows `0 < |θ_k|²` at `k = (1,0,0)`. `P` is the `Exists.some` datum of `KKernelInst` (preflight (a)(ii)).

### Name-clash grep (new public names, `RBM3D/` outside `Probe/` and outside the new file)
```
BAKhat:        0 | BAthetaSq:        0 | BAvar_lower:        0 | BAMB_perm:        0 | BAK_perm:        0 | BAK_dir_eq:        0 | BAK_dir_ge:        0 | BAKhat_eq:        0 | BAK_gap:        0 | BAK_lazy:        0 | BAK_second_moment:        0 | KSymbolInst:        0 | KSymbol_:        0
```

### Sizes (line count of `RBM3D/BA/KSymbol.lean`; preset cut P3a/P3b at 1500 lines not triggered)
```
lines  34-296  1. The variance lower bound (target 1) -/
lines 297-407  2. Coordinate permutations (target 2) and the equal w
lines 408-469  3. The per-direction bound (target 4) -/
lines 470-586  4. The symbol of `K` on the dual torus (targets 5-7) 
lines 587-693  5. The gap (target 6) -/
lines 694-756  6. The second moment (target 8) -/
lines 757-828  7. Compiled nonempty instances (`d = 3`, `L = 4`, `Λ 
total 828 lines; end of P3a (before section 4) at line 469
```
`git diff --stat main...t/T2324`: `RBM3D/BA/KSymbol.lean | 828 ++++++++++++++++++++++++++++++++++++++++++++++++++  1 file changed, 828 insertions(+)`

### Rerun (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2324`, scripts in the scratchpad directory `T2324/`)
```
$ date -u
Thu Oct  8 06:27:55 UTC 2026
$ git log -1 --format="%h %an <%ae>" ; TZ=UTC git log -1 --format=%cd --date=format-local:"%a %b %e %H:%M:%S UTC %Y"; git status --short | wc -l
cf189e6 Jun Yin <321276894+JYin80@users.noreply.github.com>
Thu Oct  8 04:55:19 UTC 2026
       0
$ git diff --stat main...t/T2324
 RBM3D/BA/KSymbol.lean | 828 ++++++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 828 insertions(+)
$ lake build RBM3D.BA.KSymbol; echo exit $?  (last line)
exit 0
Build completed successfully (3739 jobs).
$ lake env lean RBM3D/BA/KSymbol.lean; echo exit $?  (no output = no warning)
exit 0
$ lake build; echo exit $?  (last line)
exit 0
Build completed successfully (4129 jobs).
$ registry pre-check (import RBM3D; import RBM3D.BA.KSymbol; #assert_rbm_axioms)
exit 0
axiom audit: 9115 theorems, 2948 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ #print axioms of the 8 targets and 13 other new public declarations: lines equal to [propext, Classical.choice, Quot.sound]
exit 0
21 of 21 lines; lines with sorryAx: 0
$ check-file equality (eq.py) and scratch_eq.lean
(a) section-2 definitions equal (whitespace-normalized): True 466;statement BAvar_lower equal: True;statement BAMB_perm equal: True;statement BAK_dir_eq equal: True;statement BAK_dir_ge equal: True;statement BAKhat_eq equal: True;statement BAK_gap equal: True;statement BAK_lazy equal: True;statement BAK_second_moment equal: True;
lake env lean scratch_eq.lean exit 0 ; lines containing error: 0
$ report text equals file text for 8 targets and 10 instances (repcheck.py): count of True
  18 True 
$ name-clash grep (RBM3D/ outside Probe/ and outside the new file), worktree and main tree 044707b: total hits
0
$ #check of the 28 names of (c): lines
28 of 28 (names2.out, exit 0)
```

### Narrative (facts from the file and the tool log above)
- All eight targets are proved in `RBM3D/BA/KSymbol.lean`; the statements equal the check file's text (script above); no hypothesis added, no target weakened, no merged file touched (`git diff --stat`). The preset cut is not triggered: P3a ends at line 469 of 828.
- T1 `BAvar_lower` (`:185`): `BAMB_trace_eq_sum` gives `m = N^-1 sum f_i`, `f_i = (v_i - E - m)^-1`; the imaginary part gives `sum |f_i|^2 = N`; `KSymbol_double_norm_sq` gives `sum_ij |f_i - f_j|^2 = 2N^2(1-|m|^2)`; `|f_i-f_j| >= |v_i-v_j|/R^2` with `|v_i| <= 2dg`; `sum v_i = 0` and `sum v_i^2 = g^2 2dN` are `KSymbol_sum_eig`, `KSymbol_sum_eig_sq` (spectral theorem, `card_adj`, `3 <= L`).
- `|lambda_i| <= 2d` is the private `FlowPins_eig_le` (`RBM3D/BA/FlowPins.lean:734`, no public version); the file re-proves it as `KSymbol_eig_le` by copying that proof and using `card_adj` for the neighbour count. No text was taken from `../RBM1D` or `../RBM2D`, so no RBM1D/RBM2D diff-stat applies.
- T2 `BAMB_perm` (`:326`): the permutation of coordinates is an equivalence preserving `Adj` (`KSymbol_adj_perm`); `Matrix.inv_submatrix_equiv`, the pattern of `BAMB_shift` (`Ward.lean:53`).
- T3 `BAK_dir_eq` (`:392`): `Equiv.swap i j` with `BAK_perm` gives equal weights across coordinates, `BAK_zero_neg` gives equal weights for the two signs; the sum over neighbours is the sum over `unitVec` (`filter_zdistD_eq_one`, `unitVec_injective`).
- T4 `BAK_dir_ge` (`:460`): `c = kappa^2/(4(4d Lam + 3)^8)`: `BAK_adj_sum_ge` + T1 + T3; `R <= 4d Lam + 3` is `KSymbol_R_le` (`baSelf_none_of_gt`: `|E| <= 2 + 2dg`; `BAm_norm_le_one`).
- T5 `BAKhat_eq` (`:543`): `KSymbol_phi_neg` shows `theta_k.(-a) + theta_k.a` is a natural multiple of `2 pi` (`ZMod.neg_val`); with `BAK_zero_neg` the sine sum vanishes.
- T6 `BAK_gap` (`:642`): `c' = 4c/pi^2`, `c` of T4; `1 - Khat = sum K_0a (1 - cos)` by the row sum, restriction to the `2d` unit vectors, `1 - cos x >= 2x^2/pi^2` on `[0, pi]` (`Real.mul_le_sin` at `x/2`), `zdist L u <= L/2`.
- T7 `BAK_lazy` (`:567`): `1 + Khat = sum K_0a (1 + cos) >= 2 K_00 >= 2 kappa^2`; no hypothesis on `g` or `L`.
- T8 `BAK_second_moment` (`:700`): `C = max (2/mu^2 * A * S) 1` with `mu = BAct_rate`, `A = BAp5s_A`, `S = BAp5s_S`; the `max` with `1` gives `0 < C` without a proof of `S > 0`. Preflight (a) lists `C = 2AS/mu^2`, the first entry of the `max`. The diagonal term cancels exactly (`BAK_diag`); `r^2 <= (2/mu^2) e^(mu r)` is `Real.quadratic_le_exp_of_nonneg`. `2 <= d` is as pinned.
- None of the eight is a conditional adapter or special case: the hypotheses are those of the check-file statements. The constants are explicit and not optimized (preflight (a) grid: T4 slack at least 2.7e9). `P` of the instances is an `Exists.some` datum (preflight (a)(ii)), so the numbers are those of the preflight script, not of Lean.
- Time: commit `cf189e6` is dated `Thu Oct  8 04:55:19 UTC 2026` (`git log`, block "Rerun" below).

## (c) Verified Mathlib names used (`#check` in the worktree, exit 0, 28 of 28 resolve; first line of each output, cut at 100 characters)
```
@Matrix.IsHermitian.trace_eq_sum_eigenvalues : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {n : Type u_2} [in
@Matrix.IsHermitian.spectral_theorem : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {n : Type u_2} [inst_1 : F
@Matrix.inv_submatrix_equiv : ∀ {m : Type u_1} {n : Type u_2} {α : Type u_3} [inst : Fintype n] [ins
@Matrix.nonsing_inv_eq_ringInverse : ∀ {n : Type u_1} {α : Type u_2} [inst : Fintype n] [inst_1 : De
@ZMod.neg_val : ∀ {n : ℕ} [NeZero n] (a : ZMod n), (-a).val = if a = 0 then 0 else n - a.val
@Real.mul_le_sin : ∀ {x : ℝ}, 0 ≤ x → x ≤ Real.pi / 2 → 2 / Real.pi * x ≤ Real.sin x
Real.sin_sq_eq_half_sub : ∀ (x : ℝ), Real.sin x ^ 2 = 1 / 2 - Real.cos (2 * x) / 2
@Real.quadratic_le_exp_of_nonneg : ∀ {x : ℝ}, 0 ≤ x → 1 + x + x ^ 2 / 2 ≤ Real.exp x
Real.sin_nat_mul_two_pi_sub : ∀ (x : ℝ) (n : ℕ), Real.sin (↑n * (2 * Real.pi) - x) = -Real.sin x
Real.cos_nat_mul_two_pi_sub : ∀ (x : ℝ) (n : ℕ), Real.cos (↑n * (2 * Real.pi) - x) = Real.cos x
Real.cos_two_pi_sub : ∀ (x : ℝ), Real.cos (2 * Real.pi - x) = Real.cos x
Real.neg_one_le_cos : ∀ (x : ℝ), -1 ≤ Real.cos x
Real.cos_le_one : ∀ (x : ℝ), Real.cos x ≤ 1
Complex.exp_mul_I : ∀ (x : ℂ), Complex.exp (x * Complex.I) = Complex.cos x + Complex.sin x * Complex
Complex.inv_im : ∀ (z : ℂ), z⁻¹.im = -z.im / Complex.normSq z
Complex.im_ofReal_mul : ∀ (r : ℝ) (z : ℂ), (↑r * z).im = r * z.im
@Fintype.sum_bool : ∀ {α : Type u_1} [inst : AddCommMonoid α] (f : Bool → α), ∑ b, f b = f true + f 
@Fintype.sum_prod_type : ∀ {γ : Type u_1} {α₁ : Type u_2} {α₂ : Type u_3} [inst : Fintype α₁] [inst_
@Equiv.sum_comp : ∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : Fintype ι] [inst_1 : Fintyp
@inv_sub_inv : ∀ {K : Type u_1} [inst : Field K] {a b : K}, a ≠ 0 → b ≠ 0 → a⁻¹ - b⁻¹ = (b - a) / (a
@Finset.sum_image : ∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : AddCommMonoid M] {f : ι →
@Finset.sum_le_sum_of_subset_of_nonneg : ∀ {ι : Type u_1} {N : Type u_2} [inst : AddCommMonoid N] [i
@Finset.sum_pos' : ∀ {ι : Type u_1} {M : Type u_2} [inst : AddCommMonoid M] [inst_1 : Preorder M]
@Finset.add_sum_erase : ∀ {ι : Type u_1} {M : Type u_2} [inst : AddCommMonoid M] [inst_1 : Decidable
@Finset.sum_eq_single : ∀ {ι : Type u_1} {M : Type u_2} [inst : AddCommMonoid M] {s : Finset ι} {f :
@Pi.single_neg : ∀ {I : Type u_1} {f : I → Type u_2} [inst : DecidableEq I] [inst_1 : (i : I) → AddG
@Equiv.swap_apply_left : ∀ {α : Sort u_1} [inst : DecidableEq α] (a b : α), (Equiv.swap a b) a = b
@Equiv.symm_swap : ∀ {α : Sort u_1} [inst : DecidableEq α] (a b : α), Equiv.symm (Equiv.swap a b) = 
```
Verified absent: `Real.sin_sq_half`, `Real.cos_sq_half` (`grep -rln "theorem sin_sq_half\|theorem cos_sq_half\|lemma sin_sq_half" Mathlib` in `.lake/packages/mathlib` printed nothing); `Real.sin_sq_eq_half_sub` is used instead.

## (d) Open issues and paper-delta candidates
- Paper-delta D614 (ticket; large-`g` non-degeneracy, the paper has `(Mbound_AO)` only for `g < (2C)^-1`, `7_8:1891`) is the difference these targets address (per the ticket, T1, T4, T6, T8 are the Lean route for the `g`-uniform bounds). No new paper-delta candidate (`T2324a`...) from this ticket.
- Observation: `BAK_perm` (`RBM3D/BA/KSymbol.lean:346`) is public and not pinned as a target; CLAUDE.md §3 (E) asks unpinned helpers to be `private` or file-stem-prefixed; the ticket lists `BAK_perm` in its name-clash grep (`docs/tickets/T2324.md:21`). The dispatcher decides whether to keep it public; no other file uses it.
- Observation, no action required for the audit: `KSymbol_eig_le` duplicates the private `FlowPins_eig_le`; exporting the latter would remove the duplicate in a later ticket.
- Observation: preflight (a) notes that the ticket's `>= 1.01` ratio for (V) is not reproduced as a number (grid ratio >= 5.58); inequality direction holds. Section (a) is unchanged and no (a') section is needed.
- Open issues: none. BA-P4 (`BA/KHeat`) consumes T4 to T8 and `BAK_exp_moment_le`; the registry pre-check above passed with `RBM3D.BA.KSymbol` imported, the root import is left to the hub.
