Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 22:26:48 UTC 2026

Target (pin `STExpLKLKHi`, `Step6Pins.lean:301`, `(eq:Exp(L-K)1)` `6:58-62`): `𝔼ℰ^{LK×LK}_{u,σ,a} ≺ (1-u)⁻¹ (W^{-d}B_{u,0})^{11/5}` uniformly in `u ∈ [s,t]`. Notation: `B = Bctl n u = W^{-d}Bparam(·,0)`, `N = (WL)^d = W^d L^d`, `C = KDecay_tailC d`, `R_u = (1-u)⁻¹ B^{11/5}`.
Chain: off the union `S_n` of the failure events of `STLKU … 2` (factor `![x,a 1]`, `≤ N^{τ'}B²`) and `STGdecayW … 0` (factor `![a 0,y]`, `≤ N^{τ'}(B^{1/5}·STWB(|a₀-y|)e^{-√(|a₀-y|/ℓ)} + W^{-D})`, `((1-s)/(1-u))^0 = 1`), with `Σ_x ‖S_{xy}‖ = 1` (`SB_transpose`, `sum_norm_SB_row`, `3 ≤ L`):
`|ℰ| ≤ N^{2τ'}[ B²·B^{1/5}·W^dΣ_y STWB·e^{…} + N B² W^{-D} ] ≤ N^{2τ'}[ C(1-u)⁻¹B^{11/5} + N B² W^{-D} ]`.
Then `|𝔼ℰ| ≤ 𝔼|ℰ| ≤ N^{τ/2}R_u + Env_n P(S_n)` (no measurability: `‖∫f‖ ≤ ∫‖f‖`, `integral_mono_of_nonneg` against an integrable bound).

### (i) Exponent table

| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | `d` | `3` (lattice sum needs `2 ≤ d`; pin `3 ≤ d`) | `KDecay_sum_tailT_le`: `[NeZero L]` (`sz.neZeroL`), `2 ≤ d`, `0 ≤ g`, `t < 1` | `g = lam n ≥ 0` eventually (`st6_lam_pos` from `hflow.1.2.2.2.2`); `u ≤ t_n < 1` (`st5_t_lt_one`) |
| 2 | exponent of `B` | `2 + 1/5 = 11/5` | `STLKU k=2` gives `B²`, `STGdecayW` gives `B^{1/5}`; `B>0` (first term of `Bparam` `> 0` for `u<1`) | equality (exact, script: `2+1/5 = 11/5` True); no loss |
| 3 | `C = C_∞(3)` | `3·2³·radC(1/3)+1`, `radC(1/3) = 32(1+720·3⁶) = 16796192`, so `C = 403108609` | `Σ_{a∈Z_L^3} 𝒯_u(|a|_∞) ≤ C/(1-u)` uniformly in `L`, `g ≥ 0`, `u<1` | T2191 numerics `(1-t)S_t ≤ 258` (`T2191-prove.md:24`, regime (iii), `n=0,10,100`): ratio `C/258 ≥ 1.5·10⁶`; at the instance below `(1-u)S = 9.08` |
| 4 | bandwidth `𝔠`, `D = 2/𝔠` | `𝔠 = 1/6` (`sz0`), `D = 12` | `W ≥ N^𝔠` (`Bandwidth`), so `W^{-D} ≤ N^{-𝔠D} = N^{-2}` | at `n=0`: `W^{-12} = 8.67e-19` vs `N^{-2} = 2.27e-13` (factor `2.6e5`) |
| 5 | floor `B ≥ N⁻¹` | `B ≥ W^{-d}(L^d(1-u))⁻¹ = N⁻¹(1-u)⁻¹` | `0 ≤ u < 1` (`s ≥ 0`, `t < 1`) | at `n=0,u=1/2`: `B = 6.20e-5` vs `N⁻¹ = 4.77e-7` |
| 6 | absorption of `N B² W^{-D}` | `N B² W^{-D} ≤ N⁻¹B² = B^{11/5}B^{-1/5}N⁻¹ ≤ N^{-4/5}B^{11/5} ≤ (1-u)⁻¹B^{11/5}` | rows 4, 5; `N ≥ 1` | factor `N^{4/5}`; at instance `7.0e-21 ≤ 1.1e-9` |
| 7 | grid of `τ'` | `τ' = τ/3` for each input; inputs used at `(τ', D_in = D+1)` | `(C+1)N^{2τ'} ≤ N^τ`, i.e. `N^{τ/3} ≥ C+1 = 403108610` eventually; `P ≤ 2N^{-D-1} ≤ N^{-D}` needs `N ≥ 2` | conclusion-only thresholds: `N ≥ 6.6e25` (`τ=1`), `4.3e51` (`τ=1/2`), `1.5e258` (`τ=0.1`) (`∀ᶠ`, `tendsto_size`) |
| 8 | `≺ → 𝔼` parameters | `≺` used at `(τ/2, D_p = 9)` | `Env_n·P(S_n) ≤ N^{6}·2N^{-9} = 2N^{-3} ≤ N^{-11/5} ≤ R_u` (floor row 5, `(1-u)⁻¹ ≥ 1`); `N^{τ/2}R_u + R_u ≤ 2N^{τ/2}R_u ≤ N^τ R_u` | `N^{4/5} ≥ 2`, `N^{τ/2} ≥ 2` eventually; at instance `2N^{-3}/N^{-11/5} = 1.75e-5` |
| 9 | envelope `Env_n` | `W^dL^d(η_t⁻² + (1-t)⁻¹)²` with `‖𝓛^{(2)}‖ ≤ η_u⁻²` (`norm_Lloop_le`, `k+1 = 2`), `‖𝒦^{(2)}‖ ≤ ‖(W^d)⁻¹‖(1-u)⁻¹ ≤ (1-u)⁻¹` (`KLK_two_eq_kTwo`, `norm_kTwo_le`, `norm_mSigma`); window lemma with `M = f = η⁻²+(1-u)⁻¹`, `Σ_y1 = L^d` | `|E|<2` (`st6_flowE_lt_two`), `0 ≤ u < 1` | exactly `N·(…)²` |
| 10 | monotone in `u ≤ t_n` | `η_u = (1-u)Im m ≥ η_{t_n}`, `(1-u)⁻¹ ≤ (1-t_n)⁻¹` | `0 ≤ u ≤ t_n < 1`, `Im m > 0` | — |
| 11 | `Env_n ≤ N^6` (`Kenv = 6`) | `1-t ≥ Im z/(1+‖z‖) ≥ N^{-1+ε}/4` (`ST_one_sub_lemT`, `locDomain`, `‖z‖² ≤ (2-κ)²+1 < 9`); `Im m ≥ √(2κ)/2` so `(Im m)⁻² ≤ 2/κ` (`st6_mE_im_ge`, `st6_flowE_le`); `η⁻²+(1-t)⁻¹ ≤ (32/κ+4)N^{2-2ε}` | `(32/κ+4) ≤ N^{2ε}` eventually, giving `η⁻²+(1-t)⁻¹ ≤ N²`, `Env ≤ N·N⁴ = N⁵ ≤ N⁶` | slack `N¹`; for `κ=ε=1/10` the sufficient condition holds for `N ≥ 3.57e12`; the direct value at `n=0` already satisfies it (script) |
| 12 | `𝔠_d` of the pin | `1/100` | `0 < 𝔠_d ≤ 1/100`; no hypothesis of the pin involving `𝔠_d` (`STConStInd`) is used | — |
| 13 | unused premises | `s<t`, `STDriftHi`, `STLK`, `STDecay`, `STExp2` at `s`, `STConStInd`, `STStep2Core`, `STLmaxU` | the bound holds for every `u<1` (derivation above uses no window) | paper window `1-u ≥ ilambda²/L^d` of `6:58` not needed (paper-delta candidate) |
| 14 | lattice-sum match | `W^d·STWB n u K = Bparam d L lam u K` (`STWB = (W^d)⁻¹ Bparam`); `Bparam K = BparamR (K:ℝ)` (`BparamR_natCast`); `(K/ℓ)^{1/2} = √(K/ℓ)` (`Real.sqrt_eq_rpow`); both use `|1-u|` and `((K+1)^{d-2})⁻¹`, `ellT L g u`; reindex `y ↦ a-y` | `KDecay_sum_tailT_le` states `Σ_a tailT d L g t (zdistInf a) ≤ C/(1-t)` | exact match |

### (ii) One concrete nondegenerate instance

Data (merged `sz0`, `Defs/Sizes.lean:260`; `InductionDefsInst`): `d=3`, `n=0`: `L=4, W=32, lam=1/64, N=2097152=2^21`, `𝔠=1/6, 𝔡=κ=ε=1/10`, flow `z_n = 1/2 + i N^{-4/5}` (`locDomain`: `N^{-9/10} ≤ Im z`), `s=0`, `t ∈ {1/16, lemT z}`, `u = 1/2`, `a = (0,0)`, `E = 1/2` (`|E|<2`). Hypotheses of the targets: `2 ≤ 3`, `0 < 1/6`, `0 ≤ lam`, `0 ≤ s`, `t<1`, `Bandwidth 1/6` and `SizeTendsto` (merged `sz0_admissible`); `STLKU`, `STGdecayW … 0` stay hypotheses (stochastic premises of `STIngR6`, as in the merged instances; they are the paper's Steps 4, 5).
Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2222/pre.py` (pure Python; direct sums over `Z_4^3`, `msc` as the root of `m²+zm+1=0` with `Im m>0`, `lemE = -2Re m/|m|`, `lemT=|m|²`). Output:
```
N 2097152 C_inf(3) 403108609.0000002
lattice sum (W^d*STWB form) at n=0,u=1/2,a=0: 18.16442980421732  bound C/(1-u)= 806217218.0000004  ratio 2.253044142281927e-08
B(1/2)= 6.195904278883183e-05  1/N= 4.76837158203125e-07  B>=1/N: True
eta 0.4841229182759271 env(n=0,E=u=1/2) 82357489.20888886  N^6 8.507059173023462e+37
D= 12.0 W^-D 8.673617379884035e-19 N^-2 2.2737367544323206e-13 | N B^2 W^-D = 6.982960227666433e-21  <= (1-u)^-1 B^11/5 = 1.10575862342204e-09 True
z0 Im 8.763872947670244e-06 lemT 0.999990948751903 1-lemT 9.051248097025066e-06 Im z/(1+|z|) 5.842581964814335e-06 lemE 0.49999999999487965
t= 0.999990948751903 eta_t 8.763833285548397e-06 eta^-2+(1-t)^-1 13020134495.916286  N^2 4398046511104.0 True  N*e2^2 3.555173907389465e+26  N^6 8.507059173023462e+37 True
t= 0.0625 eta_t 0.907730471767983 eta^-2+(1-t)^-1 2.2802962962946394  N^2 4398046511104.0 True  N*e2^2 10904668.626265151  N^6 8.507059173023462e+37 True
asympt: (32/kappa+4)= 324.0  need <= N^(2 eps); N0= 3570467226624.0
tau 1 N0 for (C+1)N^(2tau/3)<=N^tau: N>= 6.550375898727498e+25
tau 0.5 N0 for (C+1)N^(2tau/3)<=N^tau: N>= 4.290742441463007e+51
tau 0.1 N0 for (C+1)N^(2tau/3)<=N^tau: N>= 1.454327547666486e+258
Env*2N^-9 = 2.168404344971009e-19  <= N^-11/5 = 1.2371267577238454e-14
floor R>=N^-11/5 ; slack 3-11/5 = 0.7999999999999998
exp sum 11/5 = 2+1/5: True
```
Reading: lattice sum `18.16 ≤ 8.06e8` (this is the `n=0,u=1/2` value of `inst_expLK_latticeSum`; `(1-u)S = 9.08`); envelope `8.24e7 ≤ N^6` (`inst_expLK_env`); worst flow end `t = lemT z`: `N(η⁻²+(1-t)⁻¹)² = 3.6e26 ≤ N^6 = 8.5e37` (row 11, `Kenv=6`); absorption and floors hold at the data. Nondegenerate: `N = 2^21`, `u = 1/2 ∈ [0,1)`, all sums over `|Z_4^3| = 64` points.
External hypotheses `STLKU`, `STGdecayW … 0` (concrete limit computation, TEAM §8 lesson 14): they are consumed only through `N^{τ'}`-bounds; along `sz0` (`N → ∞`) the quantities they feed behave as `(C+1)N^{2τ/3}/N^τ → 0` for every `τ>0` and `2N^{-3}/N^{-11/5} = 2N^{-4/5} → 0` (value `1.75e-5` at `N=2^21`), so no premise forces an `N`-dependent constant into the conclusion. The thresholds in row 7 are in the conclusion `∀ᶠ`, not in any hypothesis.

### Verdicts and checklist
1. Route table (the table above, against `6:58-62`): window (`STELKLKM` with factor `![x,a 1]` ← `STLKU`, `![a 0,y]` ← `STGdecayW`, `x`-sum is the column sum of the symmetric `S`), lattice sum (row 14), envelope (row 9), polynomial envelope (row 11), `≺` step (rows 4-7), `≺ → 𝔼` (rows 8-10), assembly, pin: all close with no hypothesis missing from `STExpLKLKHi`.
2. Factor assignment: confirmed from `Step2Defs.lean:110-114` (`STLKM σ ![x,a 1] * SB x y * STLKM σ ![a 0,y]`) and `Step34Pins.lean:208-216` (decay profile at `zdistInf (p.2.2 0 - p.2.2 1)`, `Cd = 0` gives `rpow 0 = 1`).
3. Consumer check (§45 O2): `ST_step6_caseIII_of_pins (hLK : STExpLKLKHi d)` (`Step6Kit.lean:737`) applies `hLK hd κ ε 𝔡 hκ hε h𝔡` then `H₁ 𝔠 sz z hflow s t hs0 hst htT hHi hLK0 hDec hExp hcon hS2 hLmax hLKU hS5` (`:740, :748-749`), the binder order of `STIngR6` (`Step6Pins.lean:111-123`: `𝔠 sz z`, `STFlow`, `s t`, `0≤s`, `s<t`, `t≤lemT`, `R`, `STLK`, `STDecay`, `STExp2`, `STConStInd`, `STStep2Core`, `STLmaxU`, `STLKU`, `STGdecayW … 0`); `inst_expLKLK_I/II/III (h : STExpLKLKHi 3)` (`Step6Kit.lean:1098-1106`) and `inst_skeleton6I/II/III (hLK : STExpLKLKHi 3)` (`:1110, :1116, :1121`) take exactly `stExpLKLKHi_holds 3`. The instances at `szB`, `zB` with `t = 15/16, 31/32` also satisfy `t<1`, `t ≤ lemT` (`lemT_zB ≥ 31/32`); the bound holds for every `u<1`, so regimes (i)-(iii) need no change.
4. §29 checklist: (1) `0 ≤ s ≤ u ≤ t ≤ lemT z < 1`, `1-u>0` everywhere; (2) window unused; (3) only `N = W^dL^d`, `W ≥ N^𝔠`; (4) hypotheses `∀ n`, conclusion eventual (`st6_prec_det_iff`); (5) uniform in `u` because both inputs are (union inside `P`); no grid lift; (6) `0 ≤ lam` eventually (`st6_lam_pos`); (7) scale `N`, `W^{-D}` converted by `Bandwidth`.
5. Registry: `Axioms.lean:230` (`STExpLKLKHi` owed line) and `:321` (`STExpLKLKHiConcl` structural) located by grep; no preflight issue.
Paper-delta candidates (for the prover to carry): (a) window `1-u ≥ ilambda²/L^d` of `6:58` not needed for the bound; (b) the `≲ (1-u)⁻¹` of `6:61` has the explicit constant `C_∞(3) = 403108609` (so the `∀ᶠ` thresholds of row 7 are large).

Verdict T2222 targets 1-4 (window, lattice sum, envelope, envelope polynomial, `expLK_prec`, `expLK_expect`, `STExpLKLKHiConcl_of_LKU`, `stExpLKLKHi_holds`, instances): PASS.

## (b) Script output
```
$ git log -1 --format="%h %an %s" t/T2222; date -u
e96b222 Jun Yin T2222: S6-06 Induction/ExpEtermsA (proves STExpLKLKHi)
Mon Oct  5 22:49:26 UTC 2026
$ git diff --stat main...t/T2222; git diff main -- RBM3D/Induction/Step6Pins.lean | wc -l
 RBM3D/Induction/ExpEtermsA.lean | 705 ++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean          |   1 -
 2 files changed, 705 insertions(+), 1 deletion(-)
0
$ git diff main...t/T2222 -- RBM3D/Test/Axioms.lean | grep "^[-+][^-+]" | cut -c1-90
-   `RBM.Gauss.Sizes.STExpLKLKHi, -- `6:58-62` (L-K)x(L-K) drift bound: S6-06; S6-01 (T220
$ grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Induction/ExpEtermsA.lean
0
$ lake build RBM3D.Induction.ExpEtermsA 2>&1 | tail -2
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3847 jobs).
$ lake env lean RBM3D/Induction/ExpEtermsA.lean; echo $?   # fresh elaboration, no output expected
0
```

### Full build and registry pre-check (CLAUDE.md §3 (A), DECISIONS §20)
With the owed line deleted, the root audit fails until the hub adds the root import (the merged `inst_expLKLK_I..III` and skeletons assume `STExpLKLKHi`; this module proves it). The full build was therefore run with a temporary, uncommitted `import RBM3D.Induction.ExpEtermsA` after the last import of `RBM3D.lean`, removed afterwards:
```
$ lake build   # temporary root import; started Mon Oct  5 22:39:49 UTC 2026; exit code 0
non-vacuity certificates: 0 of 146 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4025 jobs).
lake build  30.42s user 5.55s system 110% cpu 32.556 total
$ git status --short RBM3D.lean   # after removing the temporary line
(empty)
$ lake env lean pre_new.lean; echo $?   # pre_new.lean = import RBM3D; import RBM3D.Induction.ExpEtermsA; #assert_rbm_axioms
0
$ grep -n "STExpLKLKHi\b\|STExpLKLKHi," pre_base.out pre_new.out   # base = same run before Test.Axioms was rebuilt (cache copied from main)
base: 139:  RBM.Gauss.Sizes.STExpLKLKHi: 11 [no certificate]
new: (no match: absent from the owed ledger and from the carry-nothing list)
$ grep "premises found\|^registry" pre_base.out pre_new.out | cut -c1-110; grep -c "none of" pre_new.out
base: premises found by scanning: 126 (borrowed 1, owed 94, structural 25, refuted 6).
base: registry: 2 borrowed + 145 owed + 80 structural + 7 refuted; 108 registered premise(s) carry nothing yet
new:  premises found by scanning: 125 (borrowed 1, owed 93, structural 25, refuted 6).
new:  registry: 2 borrowed + 144 owed + 80 structural + 7 refuted; 108 registered premise(s) carry nothing yet
0
```

### Axioms (`#print axioms` on a copy of the module plus one line per name)
```
'RBM.Gauss.Sizes.expLK_window_le' axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expLK_latticeSum' axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expLK_env' axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expLK_env_poly' axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expLK_prec' axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expLK_expect' axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.STExpLKLKHiConcl_of_LKU' axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stExpLKLKHi_holds' axioms: [propext, Classical.choice, Quot.sound]
... 19 public declarations (8 targets above, 11 instances in RBM.Gauss.Step6Inst), lines with exactly [propext, Classical.choice, Quot.sound]: 19 of 19
```

### Target statements, extracted by script from `RBM3D/Induction/ExpEtermsA.lean` (header through `:=`)
```
theorem expLK_window_le {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (M : ℝ) (f : Zd d (sz.L n) → ℝ)
    (hM : ∀ x, ‖sz.STLKM n E u H σ ![x, a 1]‖ ≤ M)
    (hf : ∀ y, ‖sz.STLKM n E u H σ ![a 0, y]‖ ≤ f y) :
    ‖sz.STELKLKM n E u H σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d * M * ∑ y : Zd d (sz.L n), f y := by
theorem expLK_latticeSum {d : ℕ} (sz : Sizes d) (hd : 2 ≤ d) (n : ℕ) {u : ℝ} (hlam : 0 ≤ sz.lam n)
    (hu : u < 1) (a : Zd d (sz.L n)) :
    ((sz.W n : ℕ) : ℝ) ^ d * ∑ y : Zd d (sz.L n),
        sz.STWB n u (zdistInf d (sz.L n) (a - y)) *
          Real.exp (-(((zdistInf d (sz.L n) (a - y) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) ≤
      KDecay_tailC d / (1 - u) := by
theorem expLK_env {d : ℕ} (sz : Sizes d) (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    ‖sz.STELKLK n E u σ a ω‖ ≤
      ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d * ((etaT E u)⁻¹ ^ 2 + (1 - u)⁻¹) ^ 2 := by
theorem expLK_env_poly {d : ℕ} (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) {z : ℕ → ℂ}
    (hz : STFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (ht : ∀ n, t n ≤ lemT (z n)) :
    ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d *
        ((etaT (STflowE z n) (t n))⁻¹ ^ 2 + (1 - t n)⁻¹) ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ (6 : ℝ) := by
theorem expLK_prec {d : ℕ} (sz : Sizes d) (hd : 2 ≤ d) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (hsz : sz.SizeTendsto)
    (hband : sz.Bandwidth 𝔠) (hlam : ∀ᶠ n in atTop, 0 ≤ sz.lam n) {E s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n)
    (ht1 : ∀ n, t n < 1) (hLKU : STLKU sz E s t) (hGd : STGdecayW sz E s t 0) :
    sz.Prec (U := STIdx2 sz s t)
      (fun n p ω => ‖sz.STELKLK n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (11 / 5 : ℝ)) := by
theorem expLK_expect {d : ℕ} (sz : Sizes d) {E s t : ℕ → ℝ} {Kenv : ℝ} (hsz : sz.SizeTendsto)
    (hE : ∀ n, |E n| < 2) (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1)
    (henv : ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d *
        ((etaT (E n) (t n))⁻¹ ^ 2 + (1 - t n)⁻¹) ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ Kenv)
    (hprec : sz.Prec (U := STIdx2 sz s t)
        (fun n p ω => ‖sz.STELKLK n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (11 / 5 : ℝ))) :
    STExpLKLKHiConcl sz E s t := by
theorem STExpLKLKHiConcl_of_LKU {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε)
    {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n)
    (htT : ∀ n, t n ≤ lemT (z n)) (hLKU : STLKU sz (STflowE z) s t)
    (hGd : STGdecayW sz (STflowE z) s t 0) : STExpLKLKHiConcl sz (STflowE z) s t := by
theorem stExpLKLKHi_holds (d : ℕ) : STExpLKLKHi d := by
```

### Check-file equality (scratch = check imports + `import RBM3D.Induction.ExpEtermsA` + sections 1-2 + 8 pin examples + `example (d : ℕ) : STExpLKLKHi d := stExpLKLKHi_holds d` + 6 section-3 examples)
```
$ lake env lean check_eq.lean > check_eq.out; echo $?
0
$ grep -c "^example" check_eq.lean; grep -ci "error\|sorry\|warning" check_eq.out
15
0
```

### Compiled nonempty instances (statements = check section 3; deterministic hypotheses discharged: `2 ≤ 3`, `|1/2| < 2`, `0 ≤ 1/2 < 1`, `0 ≤ sz0.lam 0`)
```
theorem inst_expLKLK_I_holds :
    InstIng6Concl (fun sz E s t => STExpLKLKHiConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_expLKLK_I (stExpLKLKHi_holds 3)
theorem inst_expLKLK_II_holds :
    InstIng6Concl (fun sz E s t => STExpLKLKHiConcl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  inst_expLKLK_II (stExpLKLKHi_holds 3)
theorem inst_expLKLK_III_holds :
    InstIng6Concl (fun sz E s t => STExpLKLKHiConcl sz E s t) sz0 z0 sInst tInst :=
  inst_expLKLK_III (stExpLKLKHi_holds 3)
theorem inst_skeleton6III_LK :
    LWtermEXP 3 → STExpDuhamelZ 3 → STExpIntIII 3 →
      InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) sz0 z0 sInst tInst :=
  fun hLW hDu hInt => inst_skeleton6III (stExpLKLKHi_holds 3) hLW hDu hInt
theorem inst_expLK_latticeSum :
    ((sz0.W 0 : ℕ) : ℝ) ^ 3 * ∑ y : Zd 3 (sz0.L 0),
        sz0.STWB 0 (1 / 2) (zdistInf 3 (sz0.L 0) ((0 : Zd 3 (sz0.L 0)) - y)) *
          Real.exp (-(((zdistInf 3 (sz0.L 0) ((0 : Zd 3 (sz0.L 0)) - y) : ℕ) : ℝ) /
            ellT (sz0.L 0) (sz0.lam 0) (1 / 2)) ^ (1 / 2 : ℝ)) ≤
      KDecay_tailC 3 / (1 - 1 / 2) :=
  expLK_latticeSum sz0 (by norm_num) 0 (by rw [sz0_values.2.2.2]; norm_num) (by norm_num) 0
theorem inst_expLK_env :
    ∀ ω : sz0.SeqΩ,
      ‖sz0.STELKLK 0 (1 / 2) (1 / 2) ![true, false] ![(0 : Zd 3 (sz0.L 0)), 0] ω‖ ≤
        ((sz0.W 0 : ℕ) : ℝ) ^ 3 * ((sz0.L 0 : ℕ) : ℝ) ^ 3 *
          ((etaT (1 / 2) (1 / 2))⁻¹ ^ 2 + (1 - (1 / 2 : ℝ))⁻¹) ^ 2 :=
  fun ω => expLK_env sz0 0 (by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; norm_num) (by norm_num)
    (by norm_num) ![true, false] ![0, 0] ω
```
Five more in the same file, same data (statements at the lines of `grep -n "^theorem inst_expLK" RBM3D/Induction/ExpEtermsA.lean`): inst_expLK_window (:663), inst_expLK_env_poly (:674), inst_expLK_prec (:680), inst_expLK_expect (:690), inst_expLKLK_of_LKU (:699); hypotheses left open: `STLKU`, `STGdecayW … 0` (Steps 4, 5) for `inst_expLK_prec`, `inst_expLKLK_of_LKU`; the `Prec` of the decay step for `inst_expLK_expect`.

### Name clash and port
```
$ bash clash.sh | awk "{s+=\$2+0; k++} END {print k\" names, total hits: \"s}"   # grep -rnw over RBM3D, RBM3D.lean, CONTROL
20 names, total hits: 0
$ git grep -n "expLK_\|ExpEtermsA\|stExpLKLKHi_holds" main -- RBM3D RBM3D.lean | wc -l   # main = e9ef940
0
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h; git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Evolution/MLExpDrift.lean
9e0f275
 RBM2D/Evolution/MLExpDrift.lean | 124 ++++++++--------------------------------
 1 file changed, 24 insertions(+), 100 deletions(-)
$ git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Evolution/MLExpDrift.lean | sed -n "141p;610p;717p" | cut -c1-80
private theorem MLExpDrift_norm_sbSum_le (hL : 3 ≤ L) {A B : Z2 L → ℂ} {b : ℝ}
private theorem MLExpDrift_env_X (n : ℕ) {E u N : ℝ} (hE : |E| < 2) (hu : u < 1)
private theorem MLExpDrift_first_moment {Ω : Type*} [MeasurableSpace Ω] {P : Mea
```

### Narrative
- All 8 targets and 11 instances are in `RBM3D/Induction/ExpEtermsA.lean` (705 lines, 24 theorems, 5 of them private helpers `expLK_*`), commit e96b222 on `t/T2222`. `stExpLKLKHi_holds d : STExpLKLKHi d` is proved with `𝔠_d = 1/100`; `Step6Pins.lean` is untouched (diff against main empty). The statements equal the check file's section 2 (15 compiled `example`s above).
- Route, as in the ticket. `expLK_window_le`: column sum of `SB` (`SB_transpose`, `sum_norm_SB_row`). `expLK_latticeSum`: `y ↦ a - y`, `W^d · STWB = Bparam`, `BparamR_natCast`, `√x = x^{1/2}`, then the merged `KDecay_sum_tailT_le`. `expLK_env`: `norm_Lloop_le`, `KLK_two_eq_kTwo`, `norm_kTwo_le`, `norm_mSigma`, window with `M = f = η_u⁻² + (1-u)⁻¹`.
- `expLK_prec`: `StochDomAt.of_subset_union` with `hLKU 2` (factor `![x, a 1]`) and `hGd (2/𝔠)` (factor `![a 0, y]`, `((1-s)/(1-u))^0 = 1` by `Real.rpow_zero`), `τ' = τ/3`; `W^{-D} ≤ N^{-2}` by `Bandwidth` and `Real.rpow_le_rpow_of_nonpos`; the private `expLK_det_core` does the arithmetic `B² · B^{1/5} = B^{11/5}`.
- Zero-mode part: `B² N W^{-D} ≤ B² N⁻¹ ≤ B² B^{1/5} = B^{11/5} ≤ (1-u)⁻¹ B^{11/5}`, using `N⁻¹ ≤ B` (private `expLK_Bctl_ge`) and `N⁻¹ ≤ (N⁻¹)^{1/5} ≤ B^{1/5}`. This is weaker than the `N^{-4/5}` gain of (a) row 6 and suffices since `(1-u)⁻¹ ≥ 1`.
- `expLK_expect`: the private `expLK_first_moment` (copy of RBM2D `MLExpDrift_first_moment` at c9a24cf:717, unused `hB0` dropped, no measurability); `D_p = |Kenv| + 3` for an arbitrary real `Kenv` ((a) row 8 has `Kenv = 6`, `D_p = 9`); floor `R ≥ N^{-11/5}`; `2 ≤ N^{τ/2}`; envelope at `u ≤ t` by `η_u ≥ η_t`, `(1-u)⁻¹ ≤ (1-t)⁻¹`.
- Deviation from (a) row 11 (no statement changes): `expLK_env_poly` bounds `(1-t)⁻¹ ≤ η_t⁻¹` (`Im m ≤ 1` by `Complex.im_le_norm`, `norm_mE`) and uses `η_t⁻¹ ≤ N` from the private `expLK_eta_inv_le` (copy of `expAvg_eta_inv_le`, `RBM3D/Induction/ExpAvg.lean:631`, merged T2217; `expLK_Bctl_ge` copies `expAvg_Bctl_ge`, `:604`; `ExpAvg` is not imported), so `W^dL^d(η⁻²+(1-t)⁻¹)² ≤ 4N⁵ ≤ N⁶` for `N ≥ 4`; same `Kenv = 6`.
- Premises of the pin used by the proof: `STFlow`, `0 ≤ s`, `t ≤ lemT z`, `STLKU`, `STGdecayW … 0`. Unused binders of `stExpLKLKHi_holds`: `s < t`, `STDriftHi`, `STLK`, `STDecay`, `STExp2`, `STConStInd`, `STStep2Core`, `STLmaxU`. No hypothesis was added; no statement of the check file or of a merged file changed.
- For the hub (merge): the registry deletion and `import RBM3D.Induction.ExpEtermsA` in `RBM3D.lean` must be committed together. Without the import, `lake build` on this branch stopped with `axiom audit: 1 premise(s) that no theorem of this development proves are in none of ... [RBM.Gauss.Sizes.STExpLKLKHi]` (tool log of the first full build, 22:39 UTC); with it, the full build passes (above). `main` is now e9ef940 (T2220 merged after this branch's base afdb81e); `git diff --stat main...t/T2222` lists only the two files; if `Axioms.lean` conflicts in a hunk, keep the deleted lines of T2217, T2218 and this ticket (ticket merge note).
- No `sorry`, `admit`, `axiom`, `native_decide` in the file (count 0 above); the module builds with no warning of its own.

## (c) Verified Mathlib names (`#check @name` for each, script `mlcheck.lean`, 37 `#check` lines: 36 names + 1 probe)
```
$ lake env lean mlcheck.lean 2>&1 | grep error
mlcheck.lean:38:8: error(lean.unknownIdentifier): Unknown identifier `norm_integral_le_integral_norm`
```
- Present: `Real.sqrt_eq_rpow`, `MeasureTheory.norm_integral_le_integral_norm` (the root-level name is absent: the probe above), `MeasureTheory.integral_mono_of_nonneg`, `MeasureTheory.integral_indicator_const`, `MeasureTheory.measure_toMeasurable`, `MeasureTheory.measurableSet_toMeasurable`, `MeasureTheory.subset_toMeasurable`.
- Present: `Real.rpow_le_rpow_of_exponent_ge`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_le_rpow_of_nonpos` (`0 < x → x ≤ y → z ≤ 0 → y ^ z ≤ x ^ z`), `Real.rpow_le_rpow`, `Real.rpow_natCast`, `Real.rpow_neg`, `Real.rpow_add`, `Real.rpow_mul`, `Real.inv_rpow`, `Real.rpow_one`, `Real.rpow_zero`.
- Present: `one_le_inv₀`, `inv_anti₀`, `inv_le_one_of_one_le₀`, `one_le_pow₀`, `pow_le_pow_left₀`, `ENNReal.toReal_le_of_le_ofReal`, `tendsto_rpow_atTop`.
- Present: `Equiv.subLeft`, `Fintype.sum_equiv`, `Finset.single_le_sum`, `Finset.sum_comm`, `Finset.sum_add_distrib`, `Matrix.transpose_apply`, `Set.indicator_of_notMem`, `Set.indicator_of_mem`, `Complex.im_le_norm`, `Complex.norm_natCast`, `Complex.norm_le_abs_re_add_abs_im`.

## (d) Open issues and paper-delta candidates
- Open issues: none for this ticket. All eight targets are proved; the instances leave open only the stochastic premises (`STLKU`, `STGdecayW … 0`, Steps 4 and 5) and the other gates' pins (`LWtermEXP`, `STExpDuhamelZ`, `STExpIntIII`).
- `T2222a` (paper `6:58`): the window `1-u ≥ ilambda²/L^d` is not needed for the bound itself; `stExpLKLKHi_holds` holds for every `u < 1` (`STDriftHi` is an unused binder). The window is only needed for its use.
- `T2222b` (paper `6:61`): the `≲ (1-u)⁻¹` carries the explicit constant `KDecay_tailC d = d^{d-2} 2^d C(1/d) + 1` of `KDecay_sum_tailT_le` (`403108609` at `d = 3`: `python3` of `3*2^3*32*(1+720*3^6)+1`), plus the `+1` of the zero-mode part; the final constant `(KDecay_tailC d + 1)` enters only the eventual thresholds (`(C+1) N^{τ/3} ≤ N^τ`-type, `∀ᶠ n`), not the statement.
- No further candidate: no step needed a hypothesis the pin lacks.
