Prover model: claude-sonnet-5-5
## (a) Math preflight — Sat Oct  3 14:06:16 UTC 2026

Notation: `A = Alayer`, `Q = Qlayer`, `c = gapK κ`, `ι = Im m(E) = √(4-E²)/2`, `η_t = (1-t)ι`, `ξ_J = t m(σ_{J.1}) m(σ_{J.2})`.
Sources (read): ticket; RBM2D `Loop/SumZeroWard.lean` read at `c9a24cf` (2085 lines; `Qlayer_alt_one_eq_zero` :1921, `SigmaPi_alt_sumZero_le` :2002 by `git show c9a24cf:... | grep -n`) and at HEAD `9e0f275` (1684 lines): `diff` of section 4 onward (c9a24cf :937-2085 vs HEAD :611-1684) differs only in comments and in the deleted section 13 (RBM2D `Checks` instances), so line numbers below are HEAD's (section 4 = :611, 8 = :1068, 9 = :1162, 10 = :1333, 11 = :1556, 12 = :1668); merged `RBM3D/Loop/KL{Tree,Cut,SumZero,SumAll}.lean`.

### (i) Exponent table (chain (3.49) -> (3.50) -> (3.51) -> Lipschitz -> `t → 1`)
| item | value | constraint | slack / where it enters |
|---|---|---|---|
| bulk `κ`, `E` | `κ>0`, `|E| ≤ 2-κ` (so `κ ≤ 2`) | `4-E² ≥ κ(4-κ)` | equality at `|E|=2-κ` |
| `c = gapK κ = min(1, √(κ(4-κ)/2))` | `c ≤ 1`; `κ=1: 1`; `κ=0.1: 0.4416` | `c ≤ |1 - t m(s)²|` for `t∈[0,1]` (`|1-tm²|² = (1-t)²+t(4-E²)`) | `(κ,E)=(1,0)`: min_t = 1.0000 = c; `(1,1)`: 1.0000 = c (tight, t=0); `(0.1,1.9)`: 0.5933 vs c = 0.4416; `(2,0)`: 1 = c (script) |
| `η_t` | `(1-t)ι`, `ι>0` for `|E|<2` | `0 ≤ t<1` | `E=0,t=1/2`: 1/2; enters only through `(η_t)^{-(n-1)}` in (3.49)/(3.50) |
| base bound (3.49) | `|Σ_π A(σ,π)| ≤ 2^{n²} c^{-2n} η_t^{-(n-1)}`, `σ₀=+, σ_{n-1}=-`, `3 ≤ n` | from `KLK_sumAll_le` at **`W=1`, `L=3`**: bound `2^{n²}c^{-2n}(W^d η_t)^{-(n-1)}`; `1^d=1`, so `W^d` disappears | `W^d` enters only here and only as `1`. Fibre count: `|Z_3^d| = 3^d` replaces RBM2D's `9`: `Σ_π A = 3^{-d}Σ_a Σ_π Kpi`, `Σ_{a}` = `3^d` fibres each `≤ B`, so `3^{-d}·3^d·B = B` (no `d` in the final constant). Script: `E=0.7,n∈{4,6},t∈{.5,.9}`: LHS 5.99e0..5.13e4 vs bound 6.4e5..9.5e15 |
| `∏ m(σ_i)` in (3.49) | merged `KLKpi` contains it, so `Σ_π KLKpi = (W^d)^{n-1} K` exactly (`KLK_eq_sum_Kpi`, W=1: `Σ_π KLKpi = KLK`) | RBM2D had `Σ_π Kpi = (∏m)^{-1} K` and a `‖∏m‖=1` step | factor drops out of the base bound; no `‖∏ m‖=1` needed here |
| (3.50) class | `σ₀ ≠ σ_{n-1}` | closed under the cut: inside ends `(σ_{J.1},σ_{J.2})` differ (J long), outside ends `σ₀,σ_{n-1}` | in-polygon `w+1` and out-polygon `n-w+1` vertices, `w=J.2-J.1`; need `3 ≤ w+1 < n` and `3 ≤ n-w+1 < n`: `2 ≤ w ≤ n-2` (J diagonal, `(0,n-1)` excluded) |
| (3.50) bound | `|A(σ,π)| ≤ C_N η_t^{-(n-1)}` for `3 ≤ n ≤ N` | step: `t(1-t)·η^{-w}·η^{-(n-w)} = ι^{-1}η^{-(n-1)}` (exponents `(w+1-1)+(n-w+1-1)=n`, one `η` from `(1-t)=η/ι`) | recursion `C_{N+1} = C_N + B_{N+1} + (2^{(N+1)²}+1)C_N²/ι`, `B_N=2^{N²}c^{-2N}`; `κ=1,E=0`: `C_4 ≈ 10^{17}`, `C_6 ≈ 10^{97}`, `C_8 ≈ 10^{439}` (existence constant only, never evaluated; actual sup `|A|η^{n-1}` ≈ 0.47 (n=4), 0.35 (n=6) as t→1, script) |
| `Alayer_cut` prefactor | **new:** `A(σ,π) = t(1-ξ_J)·A(σ_in,∅)·A(σ_out,π∖J)`; RBM2D: `ξ_J(1-ξ_J)·…` | derivation: `Q(σ,π)=r_J Q_out Q_in` (unchanged, `Q` has no `∏m`), `r_J=ξ_J/(1-ξ_J)`; leaf products `∏_v g = ∏_in ∏_out (1-ξ_J)²`; `∏_in m·∏_out m = ∏_all m · m(σ_{J.1})m(σ_{J.2})` (both ends of `J` appear in both polygons) | ratio new/old = `1/(m(σ_{J.1})m(σ_{J.2}))`. For a **long** edge in `mSigma`: `m m' = m·m̄ = 1`, `ξ_J = t`, so new = old = `t(1-t)` numerically (script: both ≈1e-15). For generic `m`: old prefactor fails (rel. err 3.8e-2), new holds (2.5e-17). Lean: a general-`m` statement needs `m(σ_{J.1})m(σ_{J.2}) ≠ 0` (or the form `m m'·A = ξ(1-ξ)A_inA_out`); with `mSigma`+long `J` use `m m'=1` |
| flip (section 7) | `A(!σ,π) = conj A(σ,π)` | `Flong` invariant under `!`; `mSigma E (!s) = conj(mSigma E s)`; `∏ m(!σ_i) = conj ∏ m(σ_i)` | factor transforms to its conjugate, statement same as RBM2D (script: max diff 0) |
| (3.51) | `Q(t) = (1-t)^n A(σ_alt,∅)/∏ m(σ_alt_i)`, `∏ m(σ_alt_i) = (m m̄)^{n/2} = 1` (n even, `|E|≤2`) | `1-ξ_v = 1-t` on every edge of `σ_alt` (alternating, cyclic, `n` even) | RBM2D had no `∏m`; here the extra `1/∏m = 1` (copy `KLSumZero_prod_mSigma_alt`, private in `KLSumZero`) |
| `|Q(t)|` | `≤ C ι^{-(n-1)}(1-t)` | (3.50)+(3.51): `(1-t)^n·C((1-t)ι)^{-(n-1)}` | slope `|Q|/(1-t)` → 0.570 (n=4), 0.487 (n=6), 0.462 (n=8) at `E=0.7` (script) |
| Lipschitz | `‖Q(t)-Q(1)‖ ≤ K(1-t)`, `K=2^{n²}n²c^{-(n²+2)}` | edges of a layer-`∅` tree join equal charges: `|(1-tμ)⁻¹-1| ≤ c⁻¹`, `|f(t)-f(1)| ≤ (1-t)c⁻²`, `|μ|=1`; telescoping with `≤ n²` edges, `≤ 2^{n²}` trees | `c=1`: `K=1048576 (n=4)`, `2.47e12 (n=6)`, `1.18e21 (n=8)`; `W,L,d,g`-free |
| `t → 1` | `|Q(1)| ≤ M(1-t)` all `t<1`, `M=Cι^{-(n-1)}+K` | `δ=min(1,x/(2(M+1)))`, `x=|Q(1)|>0` gives contradiction | nothing numeric (limit argument); `Q(1)=0` exactly |
| final bound | `‖Σ_{δ₀=d₁} KLSigmaPi‖ ≤ 2^{n²} n c^{-n}(2/√(κ(4-κ)))η_t` | `1-t ≤ (2/√(κ(4-κ)))η_t`, i.e. `√((4-E²)/(κ(4-κ))) ≥ 1` | slack factor: `(1,0)`: 1.1547; `(1,1)`: 1.0000 (tight); `(0.1,1.9)`: 1.0000 (tight). No `W` (T2043 audit O1) |
| `d`, `L`, `g` | `d` free (no `3 ≤ d`), `3 ≤ L`, `g` free | — | `Q` and `A` are `L,d,g,W`-free (merged docstring); `L^d` only in `sum_Kpi_closed` (merged) and `3^d` in the base bound |
| `|T_SP(n)|`, `|diagonals n|` | `3,45,903`; `2,9,20` for `n=4,6,8` | `|T_SP(σ_alt,∅)| = 3,18,147` | cardinality bound `2^{n²}` used loosely |

### (ii) One concrete nondegenerate instance
Data: target 1 at `(E,n) = (0,4)` and `(1,6)`; target 2 at `κ=1, d=3, L=3, g=1/2, E=0, t=1/2, n=4, d₁=0`. Hypotheses: `0<κ`, `3 ≤ L`, `|E| ≤ 2-κ` (`|0| ≤ 1`), `t=1/2∈[0,1)`, `4 ≤ n`, `Even n`, `|E|<2` (`E=0`, `E=1`): all hold; no `NeZero`, `N=0` or empty index (27 sites, `n=4`, `t` interior). `KLSigmaPi_alt_sumZero_le` has no external hypothesis (no `Prop` input), so no limit computation is owed. Nondegeneracy: `Q(σ_alt,∅)(1/2) = 1/3 ≠ 0` (so the bound is not `0 ≤ B`), layer `|T_SP(σ_alt4,∅)|=3`, `Q(σ_alt,∅)(1)=0` is a cancellation of terms of total modulus 2.0 (E=0,n=4) and 6.5 (n=6).
Command (python3 3.9, stdlib only; script lives in the scratchpad, it is not Lean): `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2056/chk2.py`
Definitions mirrored: `TSP n` = crossing-free subsets of `diagonals n` (`Partition.lean:65-92`), `KLFlong`, `edgeR`, `Qlayer`, `Alayer` (`KLSumZero.lean:256-270`), `mE = (-E+√(4-E²) i)/2`, `mSigma`, cut maps `KLwIn, KLcol, KLshiftOut` and `sigmaIn/sigmaOut` of RBM2D (`KBoundCut.lean:44,58`).
```
== (ii-a) Q(sigma_alt,empty)|_{t=1} = sum over T_SP of prod edgeR; |T_SP(n)|, |T_SP(sigma_alt,empty)|
n=4 E=0.0 |TSP|=3 |layer|=3 Q(1)=0.000e+00+0.000e+00j |Q(1)|=0.00e+00 sum|terms|=2.000
n=4 E=0.7 |TSP|=3 |layer|=3 Q(1)=0.000e+00+0.000e+00j |Q(1)|=0.00e+00 sum|terms|=2.068
n=4 E=1.9 |TSP|=3 |layer|=3 Q(1)=-2.220e-16+0.000e+00j |Q(1)|=2.22e-16 sum|terms|=4.203
n=6 E=0.0 |TSP|=45 |layer|=18 Q(1)=0.000e+00+0.000e+00j |Q(1)|=0.00e+00 sum|terms|=6.500
n=6 E=0.7 |TSP|=45 |layer|=18 Q(1)=2.776e-17+0.000e+00j |Q(1)|=2.78e-17 sum|terms|=7.071
n=6 E=1.9 |TSP|=45 |layer|=18 Q(1)=1.776e-15-8.882e-16j |Q(1)|=1.99e-15 sum|terms|=41.896
n=8 E=0.0 |TSP|=903 |layer|=147 Q(1)=0.000e+00+0.000e+00j |Q(1)|=0.00e+00 sum|terms|=27.250
n=8 E=0.7 |TSP|=903 |layer|=147 Q(1)=1.717e-16+2.776e-17j |Q(1)|=1.74e-16 sum|terms|=31.349
n=8 E=1.9 |TSP|=903 |layer|=147 Q(1)=1.776e-15-1.915e-14j |Q(1)|=1.92e-14 sum|terms|=592.438
== E=0 exact check n=4: Q(t)=1+2((1+t)^-1-1) (merged chk_Qlayer); t=1/2 value
0.5 (0.33333333333333326+0j) 0.33333333333333326
0.9 (0.05263157894736836+0j) 0.05263157894736836
1.0 0j 0.0
== (3.51)  Q=(1-t)^n A/(prod m), prod m(sigma_alt)=1; and slope Q(t)/(1-t) as t->1 (E=0.7)
n=4 prod m=1.000000-0.000000j  |Q(t)|/(1-t) at t=.5,.9,.99,.999: ['0.7481', '0.5996', '0.5727', '0.5701']
n=6 prod m=1.000000-0.000000j  |Q(t)|/(1-t) at t=.5,.9,.99,.999: ['0.1752', '0.4576', '0.4845', '0.4868']
n=8 prod m=1.000000-0.000000j  |Q(t)|/(1-t) at t=.5,.9,.99,.999: ['0.0939', '0.3677', '0.4536', '0.4616']
== Alayer_cut: A(s,pi) vs prefactor * A(s_in,empty) * A(s_out,pi'), innermost long J, random sigma
mSigma E=0.7, t in {1/2,9/10}, n in {4,6}: cases=444 max rel|A-new|=1.29e-15  max rel|A-old(RBM2D xi(1-xi))|=1.26e-15
mSigma E=0,   t in {1/2,9/10}, n in {4,6}: cases=366 max rel|A-new|=3.29e-15  max rel|A-old(RBM2D xi(1-xi))|=3.29e-15
generic m (not unimodular): max |m m'| = 0.52 (so ||t m m'||<1 on [0,1])
generic m, t in {1/2,9/10}, n in {4,6}: cases=386 max rel|A-new|=2.45e-17  max rel|A-old(RBM2D xi(1-xi))|=3.78e-02
== (3.49) base bound: |sum_pi A(s,pi)| <= 2^{n^2} c^{-2n} eta^{-(n-1)}, s0=+, s_{n-1}=-, kappa=2-|E|
E=0.7 n=4 t=0.5 kappa=1.30 c=1.0000 eta=0.4684: max_s|sum_pi A|=5.9850e+00 <= bound 6.378e+05
E=0.7 n=4 t=0.9 kappa=1.30 c=1.0000 eta=0.0937: max_s|sum_pi A|=5.9956e+02 <= bound 7.973e+07
E=0.7 n=6 t=0.5 kappa=1.30 c=1.0000 eta=0.4684: max_s|sum_pi A|=2.1260e+01 <= bound 3.049e+12
E=0.7 n=6 t=0.9 kappa=1.30 c=1.0000 eta=0.0937: max_s|sum_pi A|=5.1298e+04 <= bound 9.527e+15
== (3.50): sup over s0!=s_{n-1}, all pi of |A| eta^{n-1} (E=0.7) as t->1 (finite C)
n=4 t=.5,.9,.99,.999: ['0.6150', '0.4928', '0.4707', '0.4686']
n=6 t=.5,.9,.99,.999: ['0.2019', '0.3301', '0.3495', '0.3511']
== flip: A(!s,pi)=conj A(s,pi) (prod m flips to its conjugate), E=0.7, t=0.9, n=6
max |A(!s)-conj A(s)| = 0
== instances: target 2 data kappa=1,E=0,t=1/2,n=4,d=3,L=3,g=1/2; Q(1/2)=(0.33333333333333326+0j)
c_kappa=1.0 eta_t=0.5  RHS=2^16*4*c^-4*(2/sqrt(3))*eta=151348.9090  LHS=|Q(1/2)|=0.3333
target 1 data: E=1,n=6: |E|<2 yes; Q(sigma_alt6,empty)(1)= (4.163336342344337e-17+0j)
```
Rows `== constants` and `== induction constants` of the same output are quoted in the table (i) (4 + 5 lines, not repeated).
Not covered by this script (Lean-side only): the layer lemma `Flong_eq_iff_cut` and `Flong_FIn/FOut` (RBM2D :611-760) are not in the public API of `KLCut`; `sigmaIn`, `sigmaOut`, `exists_innermost`, `Flong_subset_diagonals` do not exist in `RBM3D` (grep of `RBM3D/` empty): to be written here. `KLsum_cut` (public, `KLCut.lean:1297`) replaces RBM2D `sum_cut` (private there).

### Verdicts
- `Qlayer_alt_one_eq_zero` (E,n arbitrary with `|E|<2`, `4 ≤ n`, even): **PASS**. The chain closes; the only changes vs RBM2D are the `∏ m` bookkeeping above (`Alayer_cut` prefactor `t(1-ξ_J)` needing `m m' ≠ 0`, base bound without `(∏m)⁻¹`, (3.51) with `1/∏ m(σ_alt)=1`), and `9 → 3^d` in the base bound.
- `KLSigmaPi_alt_sumZero_le`: **PASS** (the merged `SigmaPi_alt_sumZero_le_of_Qlayer_one` plus target 1; no `W`, no `3 ≤ d`).
## (a′) Preflight corrections — Sat Oct  3 14:54:54 UTC 2026
One correction, no verdict changes. (a) says (row `Alayer_cut` prefactor; first Verdicts bullet) that the new prefactor `t(1-ξ_J)` needs `m(σ_{J.1}) m(σ_{J.2}) ≠ 0`
in a general-`m` Lean statement. It does not: with `ξ_J = t m_i m_j`, `t(1-ξ_J)(∏_in m)(∏_out m) = t(1-ξ_J)(∏ m) m_i m_j = ξ_J(1-ξ_J)(∏ m)`, an identity with no
division by `m_i m_j`. The compiled (private) lemma has only `hm : ‖t m_s m_s'‖ < 1` (used for `1-ξ_J ≠ 0`):
```
$ sed -n '/^private theorem Alayer_cut/,/:= by/p' RBM3D/Loop/KLSumZeroWard.lean
private theorem Alayer_cut (hn : 2 ≤ n) (m : Bool → ℂ) {t : ℝ}
    (hm : ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1) (σ : Fin n → Bool)
    {F₀ : Finset (Fin n × Fin n)} (hF₀ : F₀ ∈ TSP n) {π : Finset (Fin n × Fin n)}
    (hπ : KLFlong F₀ σ = π) (hJπ : J ∈ π) (hinner : ∀ e ∈ π, KLArcLe e J → e = J) :
    Alayer m t σ π = (t : ℂ) * (1 - t * (m (σ J.1) * m (σ J.2))) *
      Alayer m t (sigmaIn σ J) ∅ *
        Alayer m t (sigmaOut σ J) ((π.erase J).image (KLshiftOut J)) := by
```
## (b) Script output (worktree /Users/junyin/Lean_proof/RBM3D-wt/T2056, branch t/T2056; scripts in the scratchpad `T2056/`)
```
$ date -u; git log --oneline -1; wc -l RBM3D/Loop/KLSumZeroWard.lean
Sat Oct  3 14:53:52 UTC 2026
45d225d T2056: KL7c sum-zero identity Q(sigma_alt, empty)|_{t=1} = 0 and signed sum-zero bound (KLSumZeroWard)
    1265 RBM3D/Loop/KLSumZeroWard.lean
$ lake build RBM3D.Loop.KLSumZeroWard 2>&1 | tail -3
Build completed successfully (3249 jobs).
$ lake build 2>&1 | tail -1    # whole library; the root import of the new module is added by the hub at merge
Build completed successfully (3770 jobs).
$ lake env lean precheck.lean    # import RBM3D; import RBM3D.Loop.KLSumZeroWard; #assert_rbm_axioms
exit=0
axiom audit: 1780 theorems, 810 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
$ grep -n "sorry\|admit\|native_decide\|axiom " RBM3D/Loop/KLSumZeroWard.lean
grep exit=1 (1 = no match)
$ #print axioms  (every public declaration of the file: 2 targets, 10 helpers/instances)
'RBM.Loop.Qlayer_alt_one_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLSigmaPi_alt_sumZero_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLSumZeroWard_Qlayer_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLSumZeroWard_inst_Q_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLSumZeroWard_inst_Q_six' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLSumZeroWard_inst_Q_four_nondeg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLSumZeroWard_inst_Q_six_nondeg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLSumZeroWard_inst_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLSumZeroWard_inst_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLSumZeroWard_inst_bound_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLSumZeroWard_inst_bound_lhs' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLSumZeroWard_inst_bound_six' depends on axioms: [propext, Classical.choice, Quot.sound]
$ target statements, extracted by script from RBM3D/Loop/KLSumZeroWard.lean
theorem Qlayer_alt_one_eq_zero :
    ∀ E : ℝ, |E| < 2 → ∀ (n : ℕ) [NeZero n], 4 ≤ n → Even n →
      Qlayer (mSigma E) 1 (KLsigAlt n) ∅ = 0
1153:variable (d : ℕ) (g : ℝ)
theorem KLSigmaPi_alt_sumZero_le :
  ∀ κ : ℝ, 0 < κ → ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ E : ℝ, |E| ≤ 2 - κ →
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (n : ℕ) [NeZero n] (hn : 4 ≤ n), Even n → ∀ d₁ : Zd d L,
      ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d L => δ ⟨0, by omega⟩ = d₁),
          KLSigmaPi d L g (mSigma E) t (KLsigAlt n) ∅ δ‖
        ≤ 2 ^ (n ^ 2) * n * (gapK κ)⁻¹ ^ n * (2 / Real.sqrt (κ * (4 - κ))) * Gauss.etaT E t
$ statement diffs
# A: RBM2D Qlayer_alt_one_eq_zero (c9a24cf :1921), sed mSig->mSigma sigAlt->KLsigAlt, vs RBM3D
identical (diff exit 0)
# B: RBM2D SigmaPi_alt_sumZero_le (c9a24cf :2002), sed Z2 L->Zd d L, SigmaPi L->KLSigmaPi d L g, mSig->mSigma, sigAlt->KLsigAlt, etaT->Gauss.etaT, bound var d->delta, vs RBM3D
identical (diff exit 0)
# C: merged SigmaPi_alt_sumZero_le_of_Qlayer_one (KLSumZero.lean:813) vs RBM3D KLSigmaPi_alt_sumZero_le (section variables (d g) identical: grep above and KLSumZero.lean:704)
3,4c3
<     ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (n : ℕ) [NeZero n] (hn : 4 ≤ n), Even n →
<       Qlayer (mSigma E) 1 (KLsigAlt n) ∅ = 0 → ∀ d₁ : Zd d L,
---
>     ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (n : ℕ) [NeZero n] (hn : 4 ≤ n), Even n → ∀ d₁ : Zd d L,
diff exit=1 (1 = the removed hypothesis only)
704:variable (d : ℕ) (g : ℝ)
$ compiled instances (full text of the declarations; proofs are the target applied at the data)
theorem KLSumZeroWard_inst_Q_four : Qlayer (mSigma 0) 1 (KLsigAlt 4) ∅ = 0 :=
  Qlayer_alt_one_eq_zero 0 (by norm_num) 4 le_rfl (by decide)
theorem KLSumZeroWard_inst_Q_six : Qlayer (mSigma 1) 1 (KLsigAlt 6) ∅ = 0 :=
  Qlayer_alt_one_eq_zero 1 (by norm_num) 6 (by norm_num) (by decide)
theorem KLSumZeroWard_inst_bound (d₁ : Zd 3 3) :
    ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 3 => δ ⟨0, by omega⟩ = d₁),
        KLSigmaPi 3 3 (1 / 2) (mSigma 0) (1 / 2) (KLsigAlt 4) ∅ δ‖
      ≤ 2 ^ (4 ^ 2) * ((4 : ℕ) : ℝ) * (gapK 1)⁻¹ ^ 4 * (2 / Real.sqrt (1 * (4 - 1)))
          * Gauss.etaT 0 (1 / 2) :=
  KLSigmaPi_alt_sumZero_le 3 (1 / 2) 1 one_pos 3 le_rfl 0 (by norm_num) (1 / 2)
    ⟨by norm_num, by norm_num⟩ 4 le_rfl (by decide) d₁
theorem KLSumZeroWard_inst_bound_six (d₁ : Zd 3 3) :
    ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 6 → Zd 3 3 => δ ⟨0, by omega⟩ = d₁),
        KLSigmaPi 3 3 (1 / 2) (mSigma 1) (1 / 2) (KLsigAlt 6) ∅ δ‖
      ≤ 2 ^ (6 ^ 2) * ((6 : ℕ) : ℝ) * (gapK 1)⁻¹ ^ 6 * (2 / Real.sqrt (1 * (4 - 1)))
          * Gauss.etaT 1 (1 / 2) :=
  KLSigmaPi_alt_sumZero_le 3 (1 / 2) 1 one_pos 3 le_rfl 1 (by norm_num) (1 / 2)
    ⟨by norm_num, by norm_num⟩ 6 (by norm_num) (by decide) d₁
$ nondegeneracy statements
theorem KLSumZeroWard_Qlayer_zero (m : Bool → ℂ) {n : ℕ} (σ : Fin n → Bool) :
    Qlayer m 0 σ ∅ = 1
theorem KLSumZeroWard_inst_Q_four_nondeg :
    Qlayer (mSigma 0) 0 (KLsigAlt 4) ∅ ≠ Qlayer (mSigma 0) 1 (KLsigAlt 4) ∅
theorem KLSumZeroWard_inst_bound_lhs (d₁ : Zd 3 3) :
    ∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 3 => δ ⟨0, by omega⟩ = d₁),
      KLSigmaPi 3 3 (1 / 2) (mSigma 0) (1 / 2) (KLsigAlt 4) ∅ δ = 1 / 3
theorem KLSumZeroWard_inst_card :
    (KLTSPlong 4 (KLsigAlt 4) ∅).card = 3 ∧ (TSP 6).card = 45 ∧
      (KLTSPlong 6 (KLsigAlt 6) ∅).card = 18
$ name-clash grep of the 12 new public names (files containing the word): main worktree RBM3D/ + RBM3D.lean, and RBM3D-wt/*/RBM3D except T2056
names checked: 12; names with a hit: Qlayer_alt_one_eq_zero(main=0,other-worktrees=2)
  hit: /Users/junyin/Lean_proof/RBM3D-wt/T2004-audit1/RBM3D/Probe/T2004Pins.lean:1345:MAIN=('isPrimitive_Kcal','isPrimitive_eq_
  hit: /Users/junyin/Lean_proof/RBM3D-wt/T2004/RBM3D/Probe/T2004Pins.lean:1345:MAIN=('isPrimitive_Kcal','isPrimitive_eq_Kcal','
$ names absent from RBM3D (main): sigmaIn sigmaOut exists_innermost Flong_subset_diagonals KLsigmaIn KLsigmaOut
grep exit=1 (1 = none)
$ git diff --name-status main...t/T2056   (run in the main worktree)
A	RBM3D/Loop/KLSumZeroWard.lean
$ port source commits and diff-stat
RBM2D HEAD: 9e0f275; port source c9a24cf
 RBM2D/Loop/KBoundCut.lean   | 158 +++------------
 RBM2D/Loop/SumZeroWard.lean | 465 +++-----------------------------------------
 2 files changed, 54 insertions(+), 569 deletions(-)
RBM1D HEAD: de0de42; origin of prod_cut :384, Qlayer_cut :542, prod_leaves_cut :622, Alayer_cut :698, mSigma_mul_of_ne :807, exists_innermost :814, norm_Alayer_le :837 in RBM1D/Loop/SumZero.lean (070d210 per RBM2D docstring)
 RBM1D/Loop/SumZero.lean | 2 +-
 1 file changed, 1 insertion(+), 1 deletion(-)
$ python3 portmap3.py   # declaration-by-declaration comparison, RBM2D text renamed by token map
port map RBM2D SumZeroWard.lean@c9a24cf :937-1995 (sections 4-11; section 12 = target 2, diff B above) -> RBM3D KLSumZeroWard.lean; 40 declarations
SAME after token renaming (25): mem_Flong(:946), Flong_subset(:950), arcLe_le(:955), sigmaIn_shiftIn(:960), sigmaOut_shiftOut(:969), Flong_FOut(:983), Flong_FIn(:1002), Flong_eq_iff_cut(:1022), prod_cut(:1099), Qlayer_cut(:1145), fin_congr(:1196), prod_cyc(:1201), prod_leaves_cut(:1223), mSigma_not(:1359), Flong_not(:1376), Alayer_not(:1384), norm_sum_Alayer_le(:1467), KLSumZeroWard_gapK_pos(:1667), KLSumZeroWard_gapK_le_one(:1672), KLSumZeroWard_norm_edge_le(:1728), KLSumZeroWard_norm_edge_sub_le(:1742), KLSumZeroWard_norm_prod_sub_prod_le(:1765), norm_Qlayer_sub_le(:1807), sigAlt_ends(:1890), sigAlt_alt(:1897)
not re-ported (6), used from the merged public API instead: norm_mSigma, norm_mul_mSigma_lt_one (Defs/Semicircle.lean:87,91), card_Zd (Defs/Lattice.lean:67), gapK_le_norm (KLSumZero.lean:456); gapK_sq_le, norm_one_sub_sq serve only gapK_le_norm: SumZeroWard_norm_mSig(:1340), SumZeroWard_hm(:1344), SumZeroWard_card_Z2_three(:1402), SumZeroWard_gapK_sq_le(:1674), SumZeroWard_norm_one_sub_sq(:1683), SumZeroWard_gapK_le_norm(:1697)
DIFF (9): residual token spans after renaming (all spans for the 3 substantive ones, first span for the rest)
  Alayer_cut(:1299): 3 span(s)
    [* (m (σ J.1) * m (σ J.2)))] -> [: ℂ)]
    [] -> [have hPm := prod_leaves_cut hJd σ (fun s _ => m s)]
    [field_simp ring] -> [have hu : (1 - ξ) * (1 - ξ)⁻¹ = 1 := mul_inv_cancel₀ hx linear_combination ((∏ i, m (σ i)) * (∏ k : ]
  mSigma_mul_of_ne(:1352): 1 span(s)
    [[Complex.mul_conj', Gauss.norm_spectralM] -> [[Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mE]
  etaT_eq(:1364): 1 span(s)
    [by rw [Gauss.etaT, Gauss.spectralZ_im]] -> [rfl]
  norm_sum_Alayer_le_pm(:1408): 41 spans (listed in the narrative, section (b) notes 3)
  Alayer_eq_zero_of_empty(:1497): 1 span(s)
    [{n : ℕ}] -> []
  sigmaIn_ends(:1503): 1 span(s)
    [{n : ℕ}] -> []
  sigmaOut_ends(:1514): 1 span(s)
    [{n : ℕ}] -> []
  norm_Alayer_le(:1537): 1 span(s)
    [ht] -> [ht0 ht1]
  Qlayer_alt_one_eq_zero(:1921): 1 span(s)
    [] -> [rw [prod_mSigma_alt hE2 hev, one_mul]]
$ lake env lean mathlib_names.lean   # #check of the Mathlib names listed in (c)
exit=0 lines=      71 errors=0
```
### Notes (narrative; every number above is from the script output)
1. Both targets are proved with no new hypothesis and no new `Prop` (pre-check exit 0; `RBM3D/Test/Axioms.lean` untouched). One file added,
   `RBM3D/Loop/KLSumZeroWard.lean`, 1265 lines, commit 45d225d on `t/T2056`. The root import is the hub's, so the whole-library build above does not contain the
   module; the pre-check imports it.
2. Port of RBM2D `SumZeroWard.lean`@c9a24cf sections 4-12 (:937-2011; sections 4-11 compared declaration by declaration above, section 12 = target 2 = diff B);
   section 13 (RBM2D's `Z2` checks) is replaced by the instances. Sections 1-3 (:44-936) are not copied: the public `KLCut`/`KLTree` API is used (`KLsum_cut`,
   `KLFIn`, `KLFOut`, `KLshiftIn/Out`, `KLunCol_col`, `KLoutEnds_of`, `KLdiag_width`, `KLwidth_of_isDiag`, `KLshiftIn_injOn`, `KLshiftOut_injOn`); no helper of
   sections 1-3 had to be written. Private here: `sigmaIn`, `sigmaOut`, `exists_innermost`, `Flong_subset_diagonals` (public in RBM2D `KBoundCut.lean`, absent from
   RBM3D, grep above), the section-4 layer lemmas, `prod_mSigma_alt` (copy of the private `KLSumZero_prod_mSigma_alt`) and `KLSumZeroWard_{gapK_pos, gapK_le_one,
   norm_edge_le, norm_edge_sub_le, norm_prod_sub_prod_le}` (copies of helpers private in `KLSumZero.lean`; its `norm_Qlayer_le` is not needed, the Lipschitz step is
   RBM2D's `norm_Qlayer_sub_le`).
3. `norm_sum_Alayer_le_pm` (41 spans): `Z2 3 ↦ Zd 3 3` with explicit `d, g = 3, 1` in the calls of `KLK`, `KLKpi`, `sum_Kpi_closed`, `KLK_sumAll_le` (`A` is `d`- and
   `g`-free); `9 ↦ 3^3` (`card_Zd`); `Kcal_eq_sum_Kpi ↦ KLK_eq_sum_Kpi` (not in my rename map); and DECISIONS §23: `∑_π KLKpi = KLK` at `W = 1` (RBM2D: `(∏ m)⁻¹ 𝒦`),
   so `hprod`, `hprod0` and the step `‖∏ m‖ = 1` are gone. `W^d` enters only as `((1:ℝ)^3 η_t)⁻¹ = η_t⁻¹` inside `KLK_sumAll_le` at `W = 1`.
4. `Alayer_cut` (§23): RBM2D's `(t * (m_i m_j)) * (1 - t * (m_i m_j)) * A_in * A_out` becomes `(t : ℂ) * (1 - t * (m_i m_j)) * A_in * A_out` (new = old / (m_i m_j)
   when `m_i m_j ≠ 0`; see (a′)). Cause: the vertices `i`, `j` lie on both polygons, so `∏_in m · ∏_out m = (∏ m) m_i m_j`, i.e. `prod_leaves_cut` with `g s s' = m
   s` (`hPm`). At a long edge `m_i m_j = 1` (`mSigma_mul_of_ne`), so both prefactors are `t(1-t)` and the induction `norm_Alayer_le` is RBM2D's (span `ht ↦ ht0 ht1`
   only). Numeric check, (a) lines 51-54: `mSigma`, 444 cases, max rel. error of the new prefactor 1.29e-15; generic `m`, 386 cases, new 2.45e-17, RBM2D's old
   3.78e-02.
5. Other differences after renaming: `Qlayer_alt_one_eq_zero` has the extra step `rw [prod_mSigma_alt hE2 hev, one_mul]` ((3.51): `∏ m(σ^{alt}_i) = 1`, `n` even);
   `mSigma_mul_of_ne`, `etaT_eq` differ in the proof term only (merged API); `Alayer_eq_zero_of_empty`, `sigmaIn_ends`, `sigmaOut_ends`: `{n : ℕ}` binder from a
   section variable. The flip `Alayer_not` (RBM2D :1384) is token-identical: `map_prod` and `mSigma_not` carry `∏ m(σ_i)` to its conjugate.
6. Statements (diffs A-C): both targets equal RBM2D's after renaming; `KLSigmaPi_alt_sumZero_le` equals the merged adapter `SigmaPi_alt_sumZero_le_of_Qlayer_one`
   minus the hypothesis `Qlayer (mSigma E) 1 (KLsigAlt n) ∅ = 0` (same `(d g)` section binders). It is the general statement (all even `n ≥ 4`, all `d`, `g`, `L ≥
   3`, `|E| ≤ 2-κ`, `t ∈ [0,1)`, `d₁`), not a conditional adapter; no `3 ≤ d`, no `W`. The explicit constant and the bulk range `|E| ≤ 2-κ` are RBM2D's paper-delta
   T2004a-11 (cited, not re-proposed).
7. Instances: target 1 at `(E, n) = (0, 4)` and `(1, 6)`; target 2 at `κ=1, d=3, L=3, g=1/2, E=0, t=1/2, n=4` for every `d₁` (and `d₁ = 0`), and at the bulk edge `E
   = 1 = 2-κ`, `n = 6`. Every deterministic hypothesis is discharged; the targets have no external hypothesis. Nondegeneracy: the left side of the `n = 4` instance
   is `1/3`; `Q(0) = 1 ≠ 0 = Q(1)` at both target-1 instances; the layer `∅` has 3 trees (`n = 4`) and 18 of the 45 trees of the hexagon (`n = 6`), by `decide`.
8. Name clash: the only textual hit is a comment line in the unmerged `T2004` probe (both worktrees); nothing is declared under any of the 12 names elsewhere. No
   obstruction: nothing stopped, no hypothesis added, no statement weakened, no frozen or pinned signature changed, scope respected.
## (c) Verified Mathlib names (all resolved by `#check`, script above: exit 0, 0 errors; all are also used by the building file)
- `Finset.filter_image`: `Flong_FOut`, `Flong_FIn`. `Finset.prod_image`, `Finset.mul_prod_erase`, `Finset.prod_filter_mul_prod_filter_not`: `prod_cut`.
- `Finset.prod_Ico_eq_prod_range`, `Finset.prod_range_mul_prod_Ico`, `Finset.prod_Ico_consecutive`, `Finset.prod_eq_prod_Ico_succ_bot`: `prod_leaves_cut`.
- `Fin.prod_univ_castSucc`, `Fin.prod_univ_eq_prod_range`, `Fin.val_add_one_of_lt`, `Fin.last_add_one`: `prod_cyc`, `prod_leaves_cut`.
- `Finset.sum_fiberwise`: fibres `a₀ = a₁` in `norm_sum_Alayer_le_pm`. `Finset.sum_mul_sum`: `Qlayer_cut`. `Finset.add_sum_erase`: `norm_Alayer_le`.
- `Finset.sum_eq_single`, `Finset.prod_eq_zero`: `KLSumZeroWard_Qlayer_zero`.
- `Finset.card_filter_le`, `Finset.card_powerset`, `Finset.card_erase_le`, `Finset.card_insert_of_notMem`, `Finset.notMem_empty`: counting (`notMem` spelling of this
  Mathlib).
- `Finset.nonempty_iff_ne_empty`, `Finset.filter_eq_empty_iff`, `Finset.exists_min_image`, `Finset.prod_le_prod₀`: `norm_Alayer_le`, `exists_innermost`,
  `Flong_eq_iff_cut`, telescoping bound.
- `Complex.mul_conj`, `Complex.normSq_eq_norm_sq`: `mSigma_mul_of_ne` (RBM2D used `Complex.mul_conj'`). `Complex.norm_conj`, `Complex.norm_ofNat`,
  `Complex.norm_real`, `Complex.norm_of_nonneg`, `Complex.conj_ofReal`.
- `Real.norm_of_nonneg`, `Real.norm_of_nonpos`, `Real.sqrt_pos`, `inv_anti₀`, `one_le_inv₀`, `div_lt_iff₀`, `pow_le_pow_right₀`, `Nat.pow_le_pow_right`,
  `norm_sum_le`, `norm_prod`.
- Names verified absent from Mathlib: none (every name used resolved). Names verified absent from RBM3D: `sigmaIn`, `sigmaOut`, `exists_innermost`,
  `Flong_subset_diagonals`, `KLsigmaIn`, `KLsigmaOut` (grep above).
## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none new. The only Lean/paper statement differences are RBM2D's T2004a-11 (explicit constant, bulk `|E| ≤ 2-κ`; cited, not re-proposed) and
  the DECISIONS §23 factor (already signed).
- Not verified in Lean: (a)'s counts for `n = 8` (`|T_SP(8)| = 903`, `|T_SP(σ_alt,∅)| = 147`); a scratch file with a `decide +kernel` of the `n = 8` layer count did
  not finish within 600 s and was killed (the same file without it: 8 s). The file uses `n = 4, 6` only.
- KL8+9 can use `KLSigmaPi_alt_sumZero_le` as stated; `Qlayer_alt_one_eq_zero` is free of `d`, `g`, `L`, `W`. KL11 (`Kpi_cut`, RBM2D `KBoundCut.lean`) needs
  `sigmaIn`, `sigmaOut`, `exists_innermost`, `Flong_*` too; they are private here, so a public port there duplicates them without a name clash, and sharing one copy
  needs an edit of this file.
- (a′) corrects (a): no `m(σ_i) m(σ_j) ≠ 0` hypothesis is needed in `Alayer_cut`.
Report finished: Sat Oct  3 14:54:54 UTC 2026
