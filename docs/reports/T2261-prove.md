Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 06:06:06 UTC 2026

Targets (mathematics): with `a(t)=e^{-t/2}`, `b(t)=sqrt(1-e^{-t})`, `H_t = a X1 + b X2`, `X1 ~ PF g` (coordinate variances `gvarF`), `X2 ~ gueP` (`gueVar`), independent:
P1 `d/dt E Φ(H_t) = -(1/2) e^{-t} Σ_{ab} S°_{ab} E wirtSecond Φ (H_t) a b` for `t>0`; P2 the FTC form for `T ≥ 0`; T1, T2 push-forward of the band carrier onto the pair carrier; B1, B2 = P1, P2 on `ouP (UNModel.band sz) n` at `g = sz.lam n`; S `∏ Im m(z_i)` is `TestFunH` for `Im z_i > 0`. The hypotheses are only `TestFunH Φ`, `0<t` / `0≤T`, `0<Im z_i`; no external input.

### (i) Exponent table

| quantity | value | constraint | slack |
|---|---|---|---|
| `a'a` (field 1 weight) | `a' = -(1/2)e^{-t/2}`, `a'a = -(1/2)e^{-t}` | must equal the coefficient `-(1/2)e^{-t}` of P1 | equality (exact) |
| `b'b` (field 2 weight) | `b' = e^{-t}/(2b)`, `b'b = +(1/2)e^{-t}` | `a'a·v1 + b'b·v2 = -(1/2)e^{-t}(v1 - v2)` | equality (exact) |
| Stein factor per field | field 1: `v1_p · a`; field 2: `v2_p · b` (second derivative `D²Φ[B_p,B_p]` carries `a²`, `b²` through the chain rule, one factor of `a`, `b` kept in `g'`) | `E[ω_p ∂_pΦ(H)] = v_p a E[∂_p²Φ]` (resp. `b`) | equality |
| coordinate variances, diag | `v1 = S_aa`, `v2 = 1/N` (one real coordinate `(a,a,true)`) | `wirtSecond a a = coordD2 (a,a,true)` | `v1 - v2 = S°_aa` exact |
| coordinate variances, off diag `key a < key b` | `v1 = S_ab/2`, `v2 = 1/(2N)` per real coordinate `(a,b,true/false)` | ordered pairs `(a,b)`,`(b,a)` give `2 · (1/4)(∂_t²+∂_f²)` (by `Bmat_swap_true/false`, `S` symmetric) so `Σ_{a≠b} S°_ab wirt = Σ_{a<b} (S°_ab/2)(∂_t²+∂_f²)` | `v1 - v2 = S°_ab/2` exact |
| `N` | `N = card Idx d L W = (W L)^d` (`gueVar` uses `((W*L)^d : ℕ)`, `centeredVarianceEntry` uses `card Idx`) | the two must be equal (`card_Idx`) | instance: `N = 216` (pair), `2^21` (band) |
| time domain P1/B1 | `t > 0` | `b'(s) = e^{-s}/(2 sqrt(1-e^{-s}))` is decreasing in `s`, so `b'(s) ≤ b'(t/2)` for `s > t/2` (dominating bound on `Ioi (t/2)`) | finite for `t>0`; `b'(0^+) = +∞` (so `t=0` excluded) |
| time domain P2/B2 | `T ≥ 0` | integrand `(−1/2)e^{-t} Σ S° E wirt` continuous on `[0,T]` (`b'b` bounded); `E Φ(H_s)` continuous at `0` (`b(s)=0` for `s ≤ 0`, continuous) | `T=0`: both sides `0` |
| `TestFunH` constants for S (`η_i = Im z_i`, `‖V‖_op ≤ 1`, `G=(M−z)^{-1}`, `‖G‖ ≤ 1/η`) | `C0 = ∏ η_i^{-1}`; `C1 = Σ_i η_i^{-2} ∏_{j≠i} η_j^{-1}`; `C2 = Σ_i 2η_i^{-3}∏_{j≠i}η_j^{-1} + Σ_{i≠j} η_i^{-2}η_j^{-2}∏_{k≠i,j}η_k^{-1}` | `|Im m| ≤ 1/η`; `D Im m[V] = -Im N^{-1}tr(GVG)`, `≤ η^{-2}`; `D² Im m[V,V] = 2 Im N^{-1}tr(GVGVG)`, `≤ 2η^{-3}` (Hermitian `M` only; `V` any complex matrix) | finite for every `η_i > 0`; instance `(C0,C1,C2) = (0.5, 0.75, 1.75)` |
| Stein hypotheses (`GaussianProduct.stein`) | `g(ω) = DΦ(H)[B_p]`, `g'(ω) = a D²Φ(H)[B_p,B_p]` | continuous and bounded on all of `Ω`; `‖B_p‖_op = 1`; bounds `C1`, `C2` (`a ≤ 1`) | `H` Hermitian for every `ω` so the Hermitian-only bounds suffice; `v_p = 0` allowed (both sides `0`) |
| `g` (coupling) | any real | `gvarF ≥ 0` (`svarF_nonneg`, no sign condition on `g`) | none needed |
| `S°` row sums (instance sanity) | `Σ_y S_xy = 1` (`S^(B)` stochastic: `a + 2d g² a = 1`, `a = (1+2dg²)^{-1}`), so `Σ_y S°_xy = 0` | needs `L ≥ 3` (the `2d` neighbours distinct) | instance `L = 3` |
| transfer T1 | `ouMat band n t ω = ouPairMat t (Prod.map slice id ω)` | identity of formulas (`band.H = seqXmat = Xmat ∘ slice`) | exact |
| transfer T2 | `(ouP band n).map (Prod.map slice id) = (PF … (sz.lam n)).prod gueP` | `map_prod_map`, `seqP_map_slice`, `map id` (inner `this` of `ouSample_law`, `OU.lean:215-220`) | exact; forces coupling `g = sz.lam n` = the `S°` coupling (one datum) |
| `integral_map` side conditions | integrand `Φ ∘ ouPairMat t` and `wirtSecond Φ ∘ ouPairMat t` | `ouPairMat t` is continuous in `ω` and Hermitian-valued, `Φ`, `wirtSecond Φ` continuous at Hermitian points, so the composites are continuous hence measurable on `Ω × Ω` | none needed |
| consumer (UN-18, not a target) | `|E_t − E_{t*}| ≤ |E_t − E_0| + |E_{t*} − E_0| ≤ 2 · (T/2) · nf² B`, `T ≤ t* = N^{-1+τU}` (`∫_0^T (1/2)e^{-s} ds ≤ T/2`; UN-17 with `s = univ` gives `≤ (nf + nf(nf−1)) B = nf² B`) | `≤ N^ε N^{-1+Cn τU} B` holds with `Cn = 1` iff `nf² ≤ N^ε` | `N^ε/nf² → ∞` (`Admissible` contains `SizeTendsto`); `UNEMCTE2Row` is `∃ Cn`, so `Cn = 1` is available |

Consumer token check (B2 at `Φ K = ((∏_i (stieltjesN K (z i)).im : ℝ) : ℂ)`): left side `∫ ω, Φ(ouMat band n T ω) ∂ouP band n` is `((∫ ∏ Im m)  : ℂ)` by `∫ ofReal f = ofReal ∫ f` (valid for every `f`), the integral of `Pins.lean:686-688`; both `T = t` and `T = t*` use the same `E_0` term, which cancels. Right side `Σ_ab S°_ab ∫ wirtSecond Φ (ouMat band n s ω) a b` with `S° = centeredVarianceEntry d (sz.L n) (sz.W n) (sz.lam n)`; UN-17 (`OUContraction.lean:1077`, `s = univ`, `lam = sz.lam n`, `H = ouMat band n s ω`) bounds `‖Σ_ab S°_ab wirtSecond Φ H a b‖` by the `L1t d (sz.L n) (sz.W n) (sz.lam n) (ouMat band n s ω) (z u)`, `L2t …` of `Pins.lean:675-681` (`Finset.univ.erase u`, `(univ.erase u).erase v` agree with `s = univ`). UN-18 must still supply (not part of B1/B2): `Σ_ab ∫ = ∫ Σ_ab` (each `wirtSecond Φ (H) a b` is bounded by `C2` and continuous) and integrability of the weighted `L1t`, `L2t` terms (bounded by `1/η` powers, continuous at Hermitian `H`); `0 < Im z_i` from `InWindow` since `Nsz^(-1-τU) > 0`.

### (ii) One concrete nondegenerate instance

Pair instance: `d = 3`, `L = 3`, `W = 2`, `g = 1/2`, `N = 216`, `Φ = Phi2` (`z = (i, 2i)`, `η = (1, 2)`), `t = 1`, `T = 1`. Band instance: `sz0`, `n = 0` (`L = 4`, `W = 32`, `N = 2^21`, `lam = 1/64`), `t = 1`, `T = ouTStar sz0 (1/2) 0 = N^{-1/2}`. No `N = 0`, no empty index, no collapsed window; every hypothesis (`TestFunH Phi2`, `0 < t`, `0 ≤ T`, `0 < Im z_i`) holds; no external hypothesis (Stein is the merged `GaussianProduct.stein`), so the limit computation of TEAM §8 lesson 14 is not needed; the only asymptotic fact is the consumer's `N → ∞`, shown below along `sz0`.

Script 1 (scratch `.../scratchpad/T2261/inst.py`): (1) the collapse and the constant `-(1/2)e^{-t}` for an exact quadratic `Φ` on `N = 4` with random symmetric `S` (here `E Φ(H_t) = e^{-t}E_1Φ + (1-e^{-t})E_2Φ`, `E_iΦ = (1/2)Σ_p v_{i,p} D²Φ[B_p,B_p]`, `Bmat` as in `FlucVanish.lean:382`, `wirtSecond` as in `OUHessian.lean:216`); (2) `S°` at `d=3, L=3, W=2, g=1/2`; (3) `TestFunH` constants and a spot check of the bounds at a random Hermitian `K` (`N = 216`, random complex `V`, `‖V‖_op = 1`, finite differences); (4) band numbers.

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2261/inst.py`

```
dEPhi/dt (fd) = (0.05211057198251101-0.851414522440308j)
-1/2 e^-t sum S° wirt = (0.0521105719837509-0.8514145222413592j)
N= 216 a= 0.4 b=g^2 a= 0.1 row sum of S^B = 1.0
S_xx= 0.05 1/N= 0.004629629629629629 S°_xx= 0.04537037037037037
fine S shape (216, 216) row sums min/max 0.9999999999999999 1.0 sym True
S° row sums max |.| 1.6653345369377348e-16
C0,C1,C2 = 0.5 0.75 1.75
Phi(K)= 0.329907733611378 <= 0.5 | D1= -0.0009541727835626901 <= 0.75 | D2= 0.0007427836123952147 <= 1.75
sz0 n=0: N= 2097152 lam= 0.015625 t*=N^(-1/2)= 0.0006905339660024879
```

(The fine `S` of script 1 is built block-contiguously from `S^(B)(g) ⊗ 1_{W^d}/W^d`, a permutation of the `Idx` ordering; row sums and symmetry are permutation invariant.)

Script 2 (`inst2.py`), command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2261/inst2.py`

```
sz0 n=0: N= 2097152 =2^21: True S_xx= 3.047294002925402e-05 1/N= 4.76837158203125e-07 S°_xx= 2.9996102871050896e-05 >0: True
t*=N^(-1+1/2)= 0.0006905339660024879 >0: True | t=1>0, T=1>=0 for pair instance; z=(i,2i): Im=(1,2)>0
N_n=(W_n L_n)^3 with W_n L_n=128(n+1)^6, n=0..3: [2097152, 549755813888, 812479653347328, 144115188075855872]
consumer: nf^2 = 4 <= N^eps for eps=0.1 at N=2^21: 4.287093850145173 (eventually; N->inf)
```

Reading of the output: (1) the finite-difference derivative of `E Φ(H_t)` equals `-(1/2)e^{-t} Σ_{ab} S°_ab wirtSecond Φ a b` to 10 digits, confirming the sign, the factor `1/2`, the `S/2`, `1/(2N)` off-diagonal split and the ordered-pair count; `S°` has zero row sums and `S°_xx > 0`, so the instance is not collapsed; the Phi2 bounds hold with slack at a random Hermitian point.

### Verdicts

- P1 `ouGeneratorPair_hasDerivAt_integral`: PASS (hypotheses `TestFunH`, `0<t`, any real `g`, any `d`; all weights close exactly).
- P2 `ouGeneratorPair_integral_sub_eq`: PASS.
- T1 `ouMat_band_eq_ouPairMat`: PASS (identity of formulas).
- T2 `ouP_band_map_pair`: PASS (same computation as `OU.lean:215-220`; forces `g = sz.lam n`).
- B1 `ouGenerator_hasDerivAt_integral`, B2 `ouGenerator_integral_sub_eq`: PASS (consumer tokens match `Pins.lean:686-688` and UN-17 at `lam = sz.lam n`; UN-18 side conditions listed in (i)).
- S `testFunH_stieltjesImProduct`: PASS (explicit finite `C0, C1, C2` for every `η_i > 0`).
- Instances `inst_testFunH`, `inst_pair_sub_eq`, `inst_band_hasDerivAt`, `inst_band_sub_eq`: PASS (all hypotheses hold at the numbers above).

Overall verdict: PASS.

## (b) Script output — Tue Oct  6 06:14:33 UTC 2026

Commit: `335f9a2 T2261: UN-15 Universality/OUGenerator (OU generator identity, pair carrier + band ` on branch `t/T2261`; `git diff --stat main...t/T2261`:
```
 RBM3D/Universality/OUGenerator.lean | 1369 +++++++++++++++++++++++++++++++++++
 1 file changed, 1369 insertions(+)
```

Build: `lake build RBM3D.Universality.OUGenerator` (worktree `RBM3D-wt/T2261`), tail (diagnostics of other modules and header long-line lints omitted):
```
⚠ [3356/3356] Replayed RBM3D.Universality.OUGenerator
info: 1356:0: 'RBM.Univ.TestFunH' depends on axioms: [propext, Classical.choice, Quot.sound]
info: 1357:0: 'RBM.Univ.ouGeneratorPair_hasDerivAt_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
info: 1358:0: 'RBM.Univ.ouGeneratorPair_integral_sub_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
info: 1359:0: 'RBM.Univ.ouMat_band_eq_ouPairMat' depends on axioms: [propext, Classical.choice, Quot.sound]
info: 1360:0: 'RBM.Univ.ouP_band_map_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
info: 1361:0: 'RBM.Univ.ouGenerator_hasDerivAt_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
info: 1362:0: 'RBM.Univ.ouGenerator_integral_sub_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
info: 1363:0: 'RBM.Univ.testFunH_stieltjesImProduct' depends on axioms: [propext, Classical.choice, Quot.sound]
info: 1364:0: 'RBM.Univ.OUGeneratorInst.inst_testFunH' depends on axioms: [propext, Classical.choice, Quot.sound]
info: 1365:0: 'RBM.Univ.OUGeneratorInst.inst_pair_sub_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
info: 1366:0: 'RBM.Univ.OUGeneratorInst.inst_band_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
info: 1367:0: 'RBM.Univ.OUGeneratorInst.inst_band_sub_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3356 jobs).
```
Full `lake build` (worktree; root import not yet added, hub adds it): `Build completed successfully (4064 jobs).`

Sorry/axiom grep (`grep -nE 'sorry|admit|native_decide|^axiom' RBM3D/Universality/OUGenerator.lean`): exit 1 (1 = no hit).

Registry pre-check (CLAUDE.md §20): scratch `import RBM3D` + `import RBM3D.Universality.OUGenerator` + `#assert_rbm_axioms` (`regpre.lean`), `lake env lean`, exit 0; diff of its output against the same file without the OUGenerator import (`regmain.lean`):
```
1c1
< axiom audit: 7641 theorems, 2559 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
---
> axiom audit: 7656 theorems, 2563 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
```
Header of regpre output: `axiom audit: 7656 theorems, 2563 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).`; `premises found by scanning: 153 (borrowed 1, owed 97, structural 38, refuted 6, superseded 11).`. `git diff main --stat -- RBM3D/Test/Axioms.lean` is empty (Axioms.lean untouched).

Scratch check (check file + `import RBM3D.Universality.OUGenerator` + `example : T2261_<name> := @RBM.Univ.<name>` for P1, P2, T1, T2, B1, B2, S, the four instances, and `rfl` for `TestFunH`, `ouPairP`, `ouPairMat`, `OUGeneratorInst.Phi2`): `lake env lean check_scratch.lean` exit 0, `grep -c error` = 0.
```
example : T2261_ouGeneratorPair_hasDerivAt_integral := @RBM.Univ.ouGeneratorPair_hasDerivAt_integral
example : T2261_ouGeneratorPair_integral_sub_eq := @RBM.Univ.ouGeneratorPair_integral_sub_eq
example : T2261_ouMat_band_eq_ouPairMat := @RBM.Univ.ouMat_band_eq_ouPairMat
example : T2261_ouP_band_map_pair := @RBM.Univ.ouP_band_map_pair
example : T2261_ouGenerator_hasDerivAt_integral := @RBM.Univ.ouGenerator_hasDerivAt_integral
example : T2261_ouGenerator_integral_sub_eq := @RBM.Univ.ouGenerator_integral_sub_eq
example : T2261_testFunH_stieltjesImProduct := @RBM.Univ.testFunH_stieltjesImProduct
example : T2261_inst_testFunH := RBM.Univ.OUGeneratorInst.inst_testFunH
example : T2261_inst_pair_sub_eq := RBM.Univ.OUGeneratorInst.inst_pair_sub_eq
example : T2261_inst_band_hasDerivAt := RBM.Univ.OUGeneratorInst.inst_band_hasDerivAt
example : T2261_inst_band_sub_eq := RBM.Univ.OUGeneratorInst.inst_band_sub_eq
example : @RBM.Univ.TestFunH = @RBM.Univ.T2261Check.TestFunH := rfl
example : @RBM.Univ.ouPairP = @RBM.Univ.T2261Check.ouPairP := rfl
example : @RBM.Univ.ouPairMat = @RBM.Univ.T2261Check.ouPairMat := rfl
example : @RBM.Univ.OUGeneratorInst.Phi2 = @RBM.Univ.T2261Check.Phi2 := rfl
```

Name-clash grep (`git grep -nw <name> main -- 'RBM3D/*.lean' 'RBM3D.lean'`, declaration keywords only):
```
TestFunH: 0 declaration hits on main
ouPairP: 0 declaration hits on main
ouPairMat: 0 declaration hits on main
ouGeneratorPair_hasDerivAt_integral: 0 declaration hits on main
ouGeneratorPair_integral_sub_eq: 0 declaration hits on main
ouMat_band_eq_ouPairMat: 0 declaration hits on main
ouP_band_map_pair: 0 declaration hits on main
ouGenerator_hasDerivAt_integral: 0 declaration hits on main
ouGenerator_integral_sub_eq: 0 declaration hits on main
testFunH_stieltjesImProduct: 0 declaration hits on main
OUGeneratorInst: 0 declaration hits on main
```

Target statements (extracted by `awk` from the file, `theorem NAME` to `:=`):
```lean
theorem ouGeneratorPair_hasDerivAt_integral (d L W : ℕ) [NeZero L] [NeZero W] (g : ℝ)
    (Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ) (hΦ : TestFunH d L W Φ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ∫ ω, Φ (ouPairMat d L W s ω) ∂(ouPairP d L W g))
      ((-(1 / 2 : ℝ) * Real.exp (-t)) • ∑ a : Idx d L W, ∑ b : Idx d L W,
        (centeredVarianceEntry d L W g a b : ℂ) *
          ∫ ω, wirtSecond d L W Φ (ouPairMat d L W t ω) a b ∂(ouPairP d L W g)) t :=
theorem ouGeneratorPair_integral_sub_eq (d L W : ℕ) [NeZero L] [NeZero W] (g : ℝ)
    (Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ) (hΦ : TestFunH d L W Φ) (T : ℝ) (hT : 0 ≤ T) :
    (∫ ω, Φ (ouPairMat d L W T ω) ∂(ouPairP d L W g)) -
        ∫ ω, Φ (ouPairMat d L W 0 ω) ∂(ouPairP d L W g) =
      ∫ t in (0 : ℝ)..T, (-(1 / 2 : ℝ) * Real.exp (-t)) • ∑ a : Idx d L W, ∑ b : Idx d L W,
        (centeredVarianceEntry d L W g a b : ℂ) *
          ∫ ω, wirtSecond d L W Φ (ouPairMat d L W t ω) a b ∂(ouPairP d L W g) := by
theorem ouMat_band_eq_ouPairMat (d : ℕ) (sz : Sizes d) (n : ℕ) (t : ℝ)
    (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    ouMat (UNModel.band sz) n t ω =
      ouPairMat d (sz.L n) (sz.W n) t
        (Prod.map (Sizes.slice sz n) (id : Ω d (sz.L n) (sz.W n) → Ω d (sz.L n) (sz.W n)) ω) :=
theorem ouP_band_map_pair (d : ℕ) (sz : Sizes d) (n : ℕ) :
    (ouP (UNModel.band sz) n).map
        (Prod.map (Sizes.slice sz n) (id : Ω d (sz.L n) (sz.W n) → Ω d (sz.L n) (sz.W n))) =
      ouPairP d (sz.L n) (sz.W n) (sz.lam n) := by
theorem ouGenerator_hasDerivAt_integral (d : ℕ) (sz : Sizes d) (n : ℕ)
    (Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ)
    (hΦ : TestFunH d (sz.L n) (sz.W n) Φ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ∫ ω, Φ (ouMat (UNModel.band sz) n s ω) ∂(ouP (UNModel.band sz) n))
      ((-(1 / 2 : ℝ) * Real.exp (-t)) •
        ∑ a : Idx d (sz.L n) (sz.W n), ∑ b : Idx d (sz.L n) (sz.W n),
          (centeredVarianceEntry d (sz.L n) (sz.W n) (sz.lam n) a b : ℂ) *
            ∫ ω, wirtSecond d (sz.L n) (sz.W n) Φ (ouMat (UNModel.band sz) n t ω) a b
              ∂(ouP (UNModel.band sz) n)) t := by
theorem ouGenerator_integral_sub_eq (d : ℕ) (sz : Sizes d) (n : ℕ)
    (Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ)
    (hΦ : TestFunH d (sz.L n) (sz.W n) Φ) (T : ℝ) (hT : 0 ≤ T) :
    (∫ ω, Φ (ouMat (UNModel.band sz) n T ω) ∂(ouP (UNModel.band sz) n)) -
        ∫ ω, Φ (ouMat (UNModel.band sz) n 0 ω) ∂(ouP (UNModel.band sz) n) =
      ∫ t in (0 : ℝ)..T, (-(1 / 2 : ℝ) * Real.exp (-t)) •
        ∑ a : Idx d (sz.L n) (sz.W n), ∑ b : Idx d (sz.L n) (sz.W n),
          (centeredVarianceEntry d (sz.L n) (sz.W n) (sz.lam n) a b : ℂ) *
            ∫ ω, wirtSecond d (sz.L n) (sz.W n) Φ (ouMat (UNModel.band sz) n t ω) a b
              ∂(ouP (UNModel.band sz) n) := by
theorem testFunH_stieltjesImProduct (d L W : ℕ) [NeZero L] [NeZero W] (n : ℕ) (z : Fin n → ℂ)
    (hz : ∀ i, 0 < (z i).im) :
    TestFunH d L W (fun K => ((∏ i, (RBM.Univ.stieltjesN K (z i)).im : ℝ) : ℂ)) := by
```

Vocabulary (`sed -n 66,83p`, the file's `TestFunH`, `ouPairP`, `ouPairMat`; verbatim the check vocabulary, accepted by the `rfl` examples above):
```lean
`Idx L W` ↦ `Idx d L W`): `C²` near every Hermitian matrix, with the value and the first two Fréchet
derivatives bounded on Hermitian matrices. -/
def TestFunH (Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ) : Prop :=
  (∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian → ContDiffAt ℝ 2 Φ M) ∧
  (∃ C : ℝ, ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian → ‖Φ M‖ ≤ C) ∧
  (∃ C : ℝ, ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian → ‖fderiv ℝ Φ M‖ ≤ C) ∧
  (∃ C : ℝ, ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian →
    ‖fderiv ℝ (fderiv ℝ Φ) M‖ ≤ C)

/-- The pair carrier (RBM2D `ouP L W = P ⊗ gueP`, `Universality/Pins.lean:53`), law
`PF d L W g ⊗ gueP d L W`. -/
def ouPairP (g : ℝ) : Measure (Ω d L W × Ω d L W) :=
  (PF d L W g).prod (gueP d L W)

/-- The OU matrix on the pair carrier (RBM2D `ouMat L W`, `Universality/Pins.lean:59`). -/
def ouPairMat (t : ℝ) (ω : Ω d L W × Ω d L W) : Matrix (Idx d L W) (Idx d L W) ℂ :=
  Real.exp (-t / 2) • Xmat d L W ω.1 + Real.sqrt (1 - Real.exp (-t)) • Xmat d L W ω.2

```

Compiled nonempty instances (`d = 3, L = 3, W = 2, g = 1/2`; band `UNModel.band sz0`, `n = 0`): proof terms below (grep of the file); their statements are the check statements `T2261_inst_*`, accepted by the scratch-check `example`s above; every hypothesis (`TestFunH`, `0 < t`, `0 ≤ T`, `0 < Im z_i`) is discharged by `phi2_testFunH`/`zIm_pos`, `one_pos`, `zero_le_one`, `Real.rpow_nonneg`; no premise remains.
```lean
theorem phi2_testFunH : TestFunH d L W (Phi2 d L W) :=
  testFunH_stieltjesImProduct d L W 2 ![Complex.I, 2 * Complex.I] zIm_pos

theorem inst_testFunH : TestFunH 3 3 2 (Phi2 3 3 2) := phi2_testFunH 3 3 2
theorem inst_pair_sub_eq :
  ouGeneratorPair_integral_sub_eq 3 3 2 (1 / 2) _ inst_testFunH 1 zero_le_one
theorem inst_band_hasDerivAt :
  ouGenerator_hasDerivAt_integral 3 sz0 0 _ (phi2_testFunH 3 (sz0.L 0) (sz0.W 0)) 1 one_pos
theorem inst_band_sub_eq :
  ouGenerator_integral_sub_eq 3 sz0 0 _ (phi2_testFunH 3 (sz0.L 0) (sz0.W 0)) _
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)
```

Port provenance (CLAUDE.md §5.2): source RBM2D `RBM2D/Universality/OUGenerator.lean` at `c9a24cf` (1223 lines; read with `git show c9a24cf:…`). RBM2D HEAD is now `9e0f275`:
```
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Universality/OUGenerator.lean
 RBM2D/Universality/OUGenerator.lean | 104 +++++++++---------------------------
 1 file changed, 25 insertions(+), 79 deletions(-)
```
RBM1D not read. Line counts: RBM2D 1223, this file     1369 (ticket estimate 1250/1320/1450; no split needed, fallback T2261b not used).

Narrative (what was done, from the files):
- The file is the RBM2D file transformed mechanically (`Idx L W` to `Idx d L W`, `Coord` to `CoordF`, `ouP L W`/`ouMat L W` to `ouPairP d L W g`/`ouPairMat d L W`, `P`/`gvar`/`svar` to `PF`/`gvarF`/`svarF d L W g`, `gueVar d L W`), with the section-9 resolvent bridges and the transfer lemmas added; the ticket's design (pair carrier, then push-forward) was followed as written, no statement changed.
- Places where the RBM2D text did not carry over verbatim: (1) `gvar_diag/offDiag` have no RBM3D twin; the read-off `OUGenerator_gvar_eq` is `unfold gvarF; rfl`. (2) `card_Idx_eq L W` became `RBM.Gauss.card_Idx` (`(W * L)^d`); the `gueVar` read-off proof is unchanged. (3) `stieltjesN` is `Gres`-based: `OUGenerator_stieltjes_im_eq` is `simp [OUGenerator_stImCLM, stieltjesN, Gres]`; `norm_green_le` became `norm_Gsig_le_inv_eta … true` + `simpa [Gres]`; `isUnit_sub_smul_one_of_im_ne_zero` is `RBM.Ind.…`. (4) A private instance `OUGenerator_isProbabilityMeasure_ouPairP` was added (`IsFiniteMeasure (ouPairP d L W g)` is not inferred from the `def`); the implicit `g` of three private lemmas is passed as `(g := g)` (it is not determined by the arguments). (5) `omit [NeZero L] [NeZero W] in` before `OUGenerator_gvar_eq` was removed (`gvarF` needs the instances).
- T1 is `rfl`; T2 is the six-line `this` of `ouSample_law` (`OU.lean:215-220`) reproved (`Measure.map_prod_map`, `map_id`, `seqP_map_slice`); B1, B2 follow from P1, P2 at `g = sz.lam n` by `integral_map` (`OUGenerator_integral_band`: continuity of the integrand on the pair space gives `AEStronglyMeasurable`) and `simp only` of the `wirtSecond` integrals (`OUGenerator_band_wirt`).
- Not targets and not touched: every pin (`UNEMCTE2`, `UNEMCTE2Row`, `UNEMCTE2k`, `UNEMCTE2Rowk`, `UNEMCTE2RowBA` stay owed), `eq225_interval`, any kernel bound, a generator for a general `UNModel`/`ouMatC` with a mean (band only: B1, B2 are stated on `UNModel.band sz`), the `ouSample_law` route, any merged file. No registry line added or deleted (`Axioms.lean` untouched; pre-check output differs from main's only by the theorem/definition counts).
- The statements B1/B2 are special cases of the identity (band model, `g = sz.lam n`), not the general-model statement; P1/P2 are the general-`g`, general-`d` statements on the pair carrier.
- No `3 ≤ d` and no `L`–`W` relation is used; `d` enters only through `Idx d L W`, `CoordF d L W`, `usedCoords d L W`, `N = (W L)^d`.

## (c) Verified names used (all resolved by the compiled build)
- `MeasureTheory.integral_map`
- `MeasureTheory.Measure.map_prod_map`
- `MeasureTheory.integral_prod_symm / integral_prod`
- `MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
- `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`
- `RBM.Gauss.norm_Gsig_le_inv_eta (Gauss/FlowCalculus.lean:644)`
- `RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero (Induction/ConArgDet.lean:380)`
- `RBM.Gauss.card_Idx (Defs/Sizes.lean:107)`
- `RBM.Gauss.GaussianProduct.stein (Gauss/DominationAt.lean:559)`
- `RBM.Green.Xmat_eq_sum, RBM.Green.GreenDeriv_Xmat_update (Green/FlucVanish.lean:403, :529)`
- `RBM.Univ.Bmat_swap_true/false (OUHessian.lean:134, :149)`
- `RBM.Gauss.svarF_comm (Gauss/FineModel.lean:54)`
- `RBM.Gauss.Sizes.seqP_map_slice, measurable_slice (FineModel.lean:184, :178)`
- `norm_iteratedFDerivWithin_prod_le, contDiffAt_ringInverse, fderiv_inverse, Complex.ofRealCLM (as in RBM2D; Mathlib.Analysis.Calculus.ContDiff.Bounds kept)`
Names verified absent (`grep -rnE "(theorem|lemma|def) +(RBM\.Gauss\.)?(gvarF_diag|gvarF_offDiag|norm_green_le)\b" RBM3D`, no hit): `RBM.Gauss.gvarF_diag`, `gvarF_offDiag`, `RBM.Gauss.norm_green_le` (no public twin; replaced as in (b) narrative (1), (3)).

## (d) Open issues and paper-delta candidates
- **T2261a (1)** (design, no paper statement): carrier. The generator is proved on the pair carrier `PF d L W g ⊗ gueP d L W` (RBM2D's shape) and transferred to `ouP (UNModel.band sz) n` by `Prod.map (slice sz n) id` (T1, T2), not by the `ouSample_law` route of T2253a (4).
- **T2261a (2)**: the RBM2D names `ouGenerator_hasDerivAt_integral`/`_integral_sub_eq` name the band consumer form (statements on `ouP (UNModel.band sz) n`, `S°` at `sz.lam n`); the RBM2D body is `ouGeneratorPair_*`.
- **T2261a (3)**: B1, B2 are band-only (the law is Gaussian only for `UNModel.band`; `Pins.lean:600-603`); a model with a mean (`ouMatC`, BA) has a drift term not covered.
- **T2261a (4)**: RBM2D `OUGenerator.lean` changed after `c9a24cf` (diff-stat in (b): 25 insertions, 79 deletions at HEAD `9e0f275`); the port is from `c9a24cf` as the ticket states; not compared further.
- Header-comment long lines (14 lines of the module doc) trigger the `longLine` style lint before `set_option` takes effect (as in `OUHessian.lean`); no other warning from this file.
- No statement difference from the ticket's check statements; no `T2261c` candidate.
