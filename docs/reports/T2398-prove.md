Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct 10 22:40:24 UTC 2026 (`date -u`)

Citations: `B:N` = `paper/tex/B_graphical_lemmas.tex`; scripts are in the scratchpad `T2398/` (`SP`), not in the repository. Scripts model only the counters `(n_S, n_W, n_A)` of graphs (`ord = n_S + 2(n_W - n_A)`, `B:353`; waved self-loops count): they are a toy of the term list, not a proof. Lean was not run (stage 1a).

### (i) Exponent table
| # | quantity | value (script) | constraint | slack | source |
|---|---|---|---|---|---|
| 1 | `ord 𝒢^{(i)}_{xy}`, unsplit, `x≠y`, cases (1) `α=γ=β`, (2), (3), (4) distinct, (4) `α=β≠γ` | 7, 5, 5, 3, 5 | target `ord ≥ 4·1[x=y] + 5·1[x≠y]` (`B:92`) | +2, 0, 0, **-2**, 0 (case (4) needs 2 expansions, as `B:107`) | `unsplit.py`; `B:92, 107` |
| 2 | order of `GGGamma` terms (D402 coefficient, `(W-1)` as one waved `S⁺` edge) at parent `Ǧ_{y'v}Ǧ_{vy}`, `v` internal, parent `ord 0` | T1 (`S⁺MM`) **0**; T2 (`S⁺(Ǧ M + M Ǧ)`) 1; T3A, T3B (`W MS(…)`, `W = 1 + M⁺S⁺`, chain `k = 0, 1`) 1 or 2 (T3C not run: parent has no `f`) | `(eq:GGraisesord)` (`B:99`): "strictly increases" | T1: **0** (not strict); T2, T3: ≥ +1 | `ord3.py`; Lean parent counters `baGGLhs` 0, `baGGT1` 0 (T2387 probe 313) agree |
| 3 | min `ord` of the terms of `G = G°+M` (`x≠y`; `x=y`) for the five cases | (4,3,3,2,4); (4,3,3,2,4) | target 5; 4 | below 5 in every case; the all-`M` term has `(n_S,n_W,n_A) = (0,2,0)`, ord 4; the case-(4) minimum has (4,2,3), ord 2 (the term with `M̄_{xy}`) | `unsplit.py`, `allm.py` |
| 4 | **pointwise** claim `(eq:sizeGammamu_E)` at `x≠y` | not-ok leaves with paper ord, all with `x,y` in one atom: 2, 10, 10, 104, 4 (depth ≤ 4) | all leaves `≥ 5` | **-1** (pure-`M` leaf has size `W^{-2d}`, claim `(W^{-d}B)^{5/2}`) | `ord2.py`, `depth.py` |
| 5 | cause of 4: `M_{xy} = 1[same offset] M^{(B)}_{[x][y]}` | `D_xy = t² W^{-2d} Σ_c M_{ac}M_{cc}²M_{cb} M̄_{ab}` (all-`M` term of `𝒢_xy`, `S = t W^{-d} 1[same block]`) | `D_xy ≤ η_t^{-1}(W^{-d}B_{t,0})^{5/2}` | ratio ∝ `W^{d/2}`: 105.8 (g=10, W=27), 9.8 (g=1/64, W=10⁴), 3.3e3 (g=1, W=10⁴): **pointwise false** | `num.py`; `BA/GreenSchur.lean:93-99` |
| 6 | **averaged** claim (sum over `x∈[a]`, `y∈[b]`: pairs with `x,y` in one atom have equal offsets, factor `W^{-d}`) | all leaves `≥ 5` after the factor (`ord + 2` for `x~y`), max depth 2, 0 not-ok | `W^{-d} ≤ c_g^{-1} Ψ_t²`, i.e. `B_{t,0} ≥ c_g := 1/(g²+1)` (`B_{t,0} ≥ (g²+1)^{-1}`, `Defs/Params.lean:36`) | `B_{t,0}/c_g` at t=1/2: 2.07, 1.48, 8.49 for g = 1/64, 1, 10 | `ord2.py`, `depth.py`, `num.py`; averaged all-`M` ratio 7.0e-8, 2.3e-5, 5.4e-3 at W=27 (≤ 1) |
| 7 | `x = y` count (`B:68-77` omits it) | `W^{-d} ≤ (W^{-d}B_{t,0})^{1/2}` iff `B_{t,0} ≥ W^{-d}`; `B_{t,0} ≥ (L^d|1-t|)^{-1} ≥ L^{-d}`, so `L ≤ W` suffices | `L ≤ W` | `B/W^{-d}` at (L,W)=(3,27): 4.1e4, 1.5e4, 1.7e3 | `num.py` |
| 8 | `κ ≤ Im m` (`BAReal`, `BA/MFixedPoint.lean:432`), `κ := Im m / 2` | `Im m` = 0.9993, 0.6860, 0.6669 | `0 < κ ≤ Im m` | `Im m - κ` = 0.4996, 0.3430, 0.3334 | `num.py` |
| 9 | decay rate `BAct_rate(3, Λ=g, κ)` (`BA/CombesThomas.lean:45`) | 0.24982, 0.02818, 0.00277 | `‖M_ab‖ ≤ rate⁻¹ e^{-rate·|a-b|}` (`BAMfine_decay`, `BA/GreenSchur.lean:124`) | max ratio 0.25, 0.019, 0.0019 (factor ≥ 4 to 540) | `num.py` |
| 10 | `W = (1 - M⁺S)⁻¹` exists (`BAlwW`, `Graph/BAExpand.lean:82`) | `ρ(t M⁺_B)` = 0.4996, 0.4469, 0.4994 | `ρ < 1`, `0 ≤ t < 1` (`BAGGGamma`, T2387 probe 344) | `1 - ρ ≥ 0.50`; `1 - t = 1/2` | `d402.py` |
| 11 | D402 coefficient in sums 1, 2 of `GGGamma` | `max|W-1 - M⁺SW|` ≤ 1.8e-14; printed `S⁺ = SW` deviates by 7.4e-2 to 8.3e-2, `max|(W-1)_{xy}|` = 4.2e-2, 2.4e-2, 2.3e-2; `W-1 = W^{-d}[(1-tM⁺_B)⁻¹ - 1] ⊗ J` to 1.8e-14 | `(W-1) = M⁺S⁺`, `S⁺ = SW` | printed form off by more than the entries | `d402.py` (216 = 27 blocks × 8 offsets) |
| 12 | `η_t = (1-t) Im m`; `ℓ_t = min(max(g/√|1-t|, 1), L)` | η = 0.4996, 0.3430, 0.3334; ℓ_t = 1, 1.4142, 3 | `η > 0`; `0 ≤ ℓ ≤ (log W)^{10} ℓ_t` (`LWPins.lean:283-286`) | cap ≥ 1.5e5 at W=27 (`(log 27)^{10} = 1.5e5`) | `num.py` |
| 13 | certificate height (band) | `goodB' 3` (`Graph/LWExpCertBS1.lean:583`) | BA toy depth ≤ 2 (row 6) | 1 | `depth.py` |

Rows 4-6 are the content for the W3 decision: the paper's pointwise `(eq:sizeGammamu_E)` is false at BA; the averaged form closes with slack in row 6.

### (ii) One concrete nondegenerate instance
`d = 3`, `L = 3` (`3 ≤ L`), `W = 27` (`N = (WL)^3 = 531441`), `t = 1/2`, `E = 0`, `g ∈ {1/64, 1, 10}`, `κ = Im m / 2` (`m` the fixed point `m = L^{-d} tr(gΨ^B - E - m)⁻¹`, `Ψ^B` the `ℓ¹` nearest-neighbour adjacency, `Z_3^3`, degree 6). All hypotheses of the BA readings of the targets that are deterministic hold at once: `BAReal`, `0 ≤ t < 1`, `ρ < 1`, `B_{t,0} ≥ c_g`, `L ≤ W`, `ℓ` range. Stage-G pins and `STKwardgL` stay hypotheses (ticket W5).
```
$ cd SP && python3 num.py | grep -E "^--- g|W=       27|BAct_rate|t=0.5" | cut -c1-200
--- g=0.015625: m=-0.000011+0.999269j |m|=0.9993 residual 1.1e-16  Im m=0.9993  kappa:=Im m/2=0.4996  Im m-kappa=0.4996
    BAct_rate(d,Lam=g,kappa)=0.24982; max |M_ab|/(rate^-1 e^(-rate|a-b|)) = 2.496e-01 (<=1 required); max_a sum_b|M_ab| = 1.099
    t=0.5: B_t0=2.07310 (>= 1/(g^2+1)=0.99976: True)  eta_t=0.4996  ell_t=1.0000  L^d|1-t|... B>=L^-d: True
    W=       27: max_(a!=b) |D_xy| = 1.211e-04 W^-6; pointwise D/(eta^-1 Psi^5)=1.371e-03 (<=1);  averaged over x in[a],y in[b]: 6.967e-08 (<=1 ok)
--- g=1: m=-0.009172+0.686025j |m|=0.6861 residual 4.8e-16  Im m=0.6860  kappa:=Im m/2=0.3430  Im m-kappa=0.3430
    BAct_rate(d,Lam=g,kappa)=0.02818; max |M_ab|/(rate^-1 e^(-rate|a-b|)) = 1.934e-02 (<=1 required); max_a sum_b|M_ab| = 4.322
    t=0.5: B_t0=0.74074 (>= 1/(g^2+1)=0.50000: True)  eta_t=0.3430  ell_t=1.4142  L^d|1-t|... B>=L^-d: True
    W=       27: max_(a!=b) |D_xy| = 4.514e-03 W^-6; pointwise D/(eta^-1 Psi^5)=4.600e-01 (<=1);  averaged over x in[a],y in[b]: 2.337e-05 (<=1 ok)
--- g=10: m=-0.000926+0.666861j |m|=0.6669 residual 5.0e-16  Im m=0.6669  kappa:=Im m/2=0.3334  Im m-kappa=0.3334
    BAct_rate(d,Lam=g,kappa)=0.00277; max |M_ab|/(rate^-1 e^(-rate|a-b|)) = 1.850e-03 (<=1 required); max_a sum_b|M_ab| = 4.053
    t=0.5: B_t0=0.08402 (>= 1/(g^2+1)=0.00990: True)  eta_t=0.3334  ell_t=3.0000  L^d|1-t|... B>=L^-d: True
    W=       27: max_(a!=b) |D_xy| = 4.629e-03 W^-6; pointwise D/(eta^-1 Psi^5)=1.058e+02 (>1: pointwise FALSE);  averaged over x in[a],y in[b]: 5.375e-03 (<=1 ok)
$ cd SP && python3 num.py | grep "W=    10000:" | cut -c1-200      # (|D_xy| unit: W^{-2d}; pointwise ratio scales as W^{d/2}, averaged as W^{-d/2})
    W=    10000: max_(a!=b) |D_xy| = 1.211e-04 W^-6; pointwise D/(eta^-1 Psi^5)=9.774e+00 (>1: pointwise FALSE);  averaged over x in[a],y in[b]: 9.774e-12 (<=1 ok)
    W=    10000: max_(a!=b) |D_xy| = 4.514e-03 W^-6; pointwise D/(eta^-1 Psi^5)=3.279e+03 (>1: pointwise FALSE);  averaged over x in[a],y in[b]: 3.279e-09 (<=1 ok)
    W=    10000: max_(a!=b) |D_xy| = 4.629e-03 W^-6; pointwise D/(eta^-1 Psi^5)=7.541e+05 (>1: pointwise FALSE);  averaged over x in[a],y in[b]: 7.541e-07 (<=1 ok)
$ cd SP && python3 d402.py | cut -c1-130
g=0.015625: |W-1 - M+SW|_max=1.17e-14; |W-1 - blockform|_max=1.07e-14; |(W-1) - S W|_max (printed S+ instead of M+S+) = 8.33e-02; rho(t M+B)=0.4996; max|(W-1)_xy|=4.163e-02 (Q^-1=0.125)
g=1: |W-1 - M+SW|_max=1.80e-14; |W-1 - blockform|_max=1.76e-14; |(W-1) - S W|_max (printed S+ instead of M+S+) = 7.43e-02; rho(t M+B)=0.4469; max|(W-1)_xy|=2.365e-02 (Q^-1=0.125)
g=10: |W-1 - M+SW|_max=1.25e-14; |W-1 - blockform|_max=1.22e-14; |(W-1) - S W|_max (printed S+ instead of M+S+) = 7.38e-02; rho(t M+B)=0.4994; max|(W-1)_xy|=2.251e-02 (Q^-1=0.125)
$ cd SP && python3 unsplit.py; python3 ord3.py | grep -E "baGGLhs|T1 |T2a"
1 a=c=b            unsplit ord (x!=y) = 7; min over G=G°+M split terms: x!=y 4, x=y 4
2 a=c!=b           unsplit ord (x!=y) = 5; min over G=G°+M split terms: x!=y 3, x=y 3
3 a!=c=b           unsplit ord (x!=y) = 5; min over G=G°+M split terms: x!=y 3, x=y 3
4 a,c,b distinct   unsplit ord (x!=y) = 3; min over G=G°+M split terms: x!=y 2, x=y 2
4 a=b!=c           unsplit ord (x!=y) = 5; min over G=G°+M split terms: x!=y 4, x=y 4
baGGLhs ord (Lean 0): 0
  parent-without-f  T1    split-term ord=0  (nS,nW,nA)=(0,1,1)
  parent-without-f  T2a   split-term ord=1  (nS,nW,nA)=(1,1,1)
$ cd SP && python3 depth.py        # recipe: expand at the first internal vertex with two same-charge Ǧ edges until ord >= target
x!=y 1 a=c=b            paper-ord: maxdepth=1 not-ok=2 | adjusted: maxdepth=0 not-ok=0 deep=0
x!=y 2 a=c!=b           paper-ord: maxdepth=2 not-ok=10 | adjusted: maxdepth=1 not-ok=0 deep=0
x!=y 3 a!=c=b           paper-ord: maxdepth=2 not-ok=10 | adjusted: maxdepth=1 not-ok=0 deep=0
x!=y 4 a,c,b distinct   paper-ord: maxdepth=4 not-ok=104 | adjusted: maxdepth=2 not-ok=0 deep=0
x!=y 4 a=b!=c           paper-ord: maxdepth=2 not-ok=4 | adjusted: maxdepth=0 not-ok=0 deep=0
x=y  1 a=c=b            paper-ord: maxdepth=0 not-ok=0 | adjusted: maxdepth=0 not-ok=0 deep=0
x=y  2 a=c!=b           paper-ord: maxdepth=1 not-ok=0 | adjusted: maxdepth=1 not-ok=0 deep=0
x=y  3 a!=c=b           paper-ord: maxdepth=1 not-ok=0 | adjusted: maxdepth=1 not-ok=0 deep=0
x=y  4 a,c,b distinct   paper-ord: maxdepth=2 not-ok=0 | adjusted: maxdepth=2 not-ok=0 deep=0
x=y  4 a=b!=c           paper-ord: maxdepth=0 not-ok=0 | adjusted: maxdepth=0 not-ok=0 deep=0
$ cd SP && python3 allm.py | cut -c1-135
1 a=c=b            all-M term (nS,nW,nA)=(0, 2, 0) ord=4; a min-ord split term (nS,nW,nA)=(2, 2, 1) ord=4 solid=[('X', 'A', '+'), ('A', 'Y', '+')]
4 a,c,b distinct   all-M term (nS,nW,nA)=(0, 2, 0) ord=4; a min-ord split term (nS,nW,nA)=(4, 2, 3) ord=2 solid=[('X', 'A', '+'), ('A', 'C', '+'), ('C', 'B', '+'), ('B', 'Y', '+')]
```
External hypotheses (stage-G `(initialGT2)` window, `(LW_assm_exp)`): concrete limit at the merged sequence `sz0` (`Defs/Sizes.lean:260`), `Ψ_n = W_n^{-1/2}`:
```
$ cd SP && python3 limit.py
n=      0 L=4 W=3.200e+01 L<=W:True  log_W Psi=-0.5 in [-1.5,-0.1]:True  log_W lam=-1.2000  log_W L=0.4000
n=     10 L=44 W=5.154e+06 L<=W:True  log_W Psi=-0.5 in [-1.5,-0.1]:True  log_W lam=-1.2000  log_W L=0.2448
n=   1000 L=4004 W=3.216e+16 L<=W:True  log_W Psi=-0.5 in [-1.5,-0.1]:True  log_W lam=-1.2000  log_W L=0.2182
n=1000000 L=4000004 W=3.200e+31 L<=W:True  log_W Psi=-0.5 in [-1.5,-0.1]:True  log_W lam=-1.2000  log_W L=0.2096
```

### Verdicts
- **W1 (BA term list): PASS.** `GGGamma` at `α` with `y' = x`, `y = y`, `f = tr(Ǧ E_{a₁}) Ḡ_{xy}` gives T1, T2a, T2b, T3A, T3B, T3C × `k ∈ {0,1}` (rows 2, 11). Orders are computed (row 2); the first sum keeps the parent's order.
- **W2 (generic interface): PASS** (hypotheses satisfiable, no exponent obstruction). Derived from `BAMfine_eq` (not scripted): in T2 the factor `M_{xβ}` ties the offsets of `x` and `β`, so `Σ_{x∈[a],β∈[c]}` is the block loop `𝓛^{(2)}_{(-,+),(a,b)}` only for `[β] = [x]`; the terms with `[β] ≠ [x]` are offset-tied loops, not `Lloop`. Whether `LWExpI1K`, `LWExpI23K`, `LWExpI41K` (`LWExpTerm2.lean:81, 96, 115`) fit is a 1b decision.
- **W3 (lever C): PASS with a finding.** The pointwise `(eq:sizeGammamu_E)` (`B:92`) is false at BA (rows 3-5); the averaged form closes (row 6, depth ≤ 2, slack row 6). A direct proof (C) must state the averaged form; `(eq:GGraisesord)` fails for T1 (row 2).
- **W4 (identity in expectation): PASS.** The coefficient algebra needs `W-1 = M⁺SW` (row 11, verified); the expectation identity itself is not re-run here (T2387 B10).
- **W5, C1/L5, row table: PASS.** Constants and exponents hold at `g = 1/64, 1, 10` (rows 6-12); no `g ≤ W^{-ε}`, no smallness of `M - m₀ I` is used.

## (b) Script output — Sun Oct 11 00:11:24 UTC 2026 (`date -u`)

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2398`, branch `t/T2398`, commits `2e23b9f`, `e32530a`, `5f96301`, `5c62eb7`, `fdc8c57`, `2257f54` (the probe, one file). `SP` = scratchpad subdirectory `T2398/` (scripts, not in the repository). Design: `docs/reports/T2398-design.md`.
```
$ lake build RBM3D.Probe.T2398Pins | tail -3

Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3975 jobs).
$ lake build RBM3D.Probe.T2398Pins 2>&1 | grep -c "Probe/T2398Pins"      # warnings of the probe itself; the `Note` above is from upstream modules (`⚠ Replayed RBM3D.BA.LWPinsBA`, `BA.CouplingWindow`, `BA.GreenSchur`)
0
$ (lake env lean RBM3D/Probe/T2398Pins.lean ; echo "lake env lean RBM3D/Probe/T2398Pins.lean: exit $?")
lake env lean RBM3D/Probe/T2398Pins.lean: exit 0
$ SP/axcheck.sh     # `lake env lean SP/Ax.lean` (`#print axioms` of the 36 top-level declarations of the probe: 35 named, one anonymous `Decidable` instance; Ax.lean generated from the file by `SP/genAx.py`), wrapped lines joined, names replaced by X, `sort | uniq -c`
  36 X depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nwE "sorry|admit|axiom|native_decide" RBM3D/Probe/T2398Pins.lean ; echo grep exit $?
grep exit 1
$ SP/clash2.sh     # grep -rnw of each of the 36 new names in RBM3D/ and RBM3D.lean outside the probe: matches per name, `uniq -c`
  36 0
$ git diff --stat main...t/T2398
 RBM3D/Probe/T2398Pins.lean | 399 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 399 insertions(+)
$ wc -l RBM3D/Probe/T2398Pins.lean /Users/junyin/Lean_proof/RBM3D/docs/reports/T2398-design.md
     399 RBM3D/Probe/T2398Pins.lean
     169 /Users/junyin/Lean_proof/RBM3D/docs/reports/T2398-design.md
     568 total
```
**Statements extracted by script** (`python3 SP/extract.py <names>`; probe line first). The pins are the targets of this design ticket; there is no endpoint theorem to prove.
```
149: def BAG5Identity (d : ℕ) (Ls : Bool → Bool → List (BAPGraph (Fin 2))) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (E : ℂ) m → 0 ≤ t → t < 1 →
    ∀ (k s : Bool) (x y : Idx d L W),
      ∫ ω, (baG5Graph k s).val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0) =
        ((Ls k s).map fun q => ∫ ω, q.val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0)).sum
158: def BAG5Tgt (P : BAPGraph (Fin 2)) : Prop :=
  5 ≤ P.scalingOrder + (if P.g.atom (Sum.inl (P.ext 0)) = P.g.atom (Sum.inl (P.ext 1)) then 2 else 0)
163: def BAG5Leaf (P : BAPGraph (Fin 2)) : Prop := BAG5Tgt P ∧ P.g.nM ≤ 1 ∧ 2 ≤ P.g.nW
166: def BAG5Expand (Ls : Bool → Bool → List (BAPGraph (Fin 2))) : Prop := ∀ k s, ∀ q ∈ Ls k s, BAG5Leaf q
56: theorem ba_pointwise_fails : ¬ (5 ≤ baAllM.scalingOrder) ∧ (Sum.inl 1 : Fin 2 ⊕ Fin 1) ∈ baAllM.atom (.inl 0) :=
97: theorem baTwB_stuck : baTwB.scalingOrder = 3 ∧ ¬ HasGGCand baTwB ∧ (Sum.inl 1 : Fin 2 ⊕ Fin 4) ∉ baTwB.atom (.inl 0)
184: theorem ba_xy_count {d : ℕ} (sz : Sizes d) (n : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (sz.lam n ^ 2 + 1) * sz.Bctl n s
281: def BATwistLaw (μ : Measure sz.SeqΩ) (τ : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => Zd d (sz.L n) × Zd d (sz.L n)) (fun n p ω => ‖twTr C n (τ n) ω p.1 p.2‖)
      (fun n _ _ => sz.Bctl n (τ n)) ∧
    ∃ Kt : ∀ n : ℕ, Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → ℂ, (∀ n a c₁ c₂, ‖Kt n a c₁ c₂‖ ≤ sz.Bctl n (τ n)) ∧
      PrecL sz μ (U := fun n => Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n))
        (fun n p ω => ‖twL2 C n (τ n) ω p.1 p.2.1 p.2.2 - Kt n p.1 p.2.1 p.2.2‖)
        (fun n _ _ => sz.Bctl n (τ n) ^ (3 / 2 : ℝ))
357: def BAGraphPrecJoin (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      STLocalEntrygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t → ∀ P : BAPGraph (Fin 2), P.g.Normal → P.g.nM = 0 →
        PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
          (fun n p _ => ‖∫ ω, P.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n)
            (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (sz.slice n ω)) ![p.1, p.2] ∂(Sizes.seqP (sz.withLam 0))‖)
          (fun n _ _ => (t n) ^ P.g.nW * ((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ ((P.scalingOrder : ℝ) / 2))
353: abbrev BALWCutExp : ℕ → Prop := baPin LWCutExpG
```
**Compiled instances** (non-vacuity; the Step 1/2 bounds stay hypotheses, as in `BA/LWPinsBA.lean`):
```
example : BAG5Leaf { E' := Fin 2, I' := Fin 1, ext := id, ext_surj := Function.surjective_id, g := baAllM } := by
  have hA : baAllM.atom (Sum.inl 0) = baAllM.atom (Sum.inl 1) := by decide
  have hn : baAllM.nM = 0 ∧ baAllM.nW = 2 := by decide
  refine ⟨?_, ?_, ?_⟩
  · change 5 ≤ baAllM.scalingOrder + (if baAllM.atom (Sum.inl 0) = baAllM.atom (Sum.inl 1) then 2 else 0)
    simp only [hA, ite_true, baAllM_ord]
    norm_num
  · change baAllM.nM ≤ 1
    rw [hn.1]; norm_num
  · change 2 ≤ baAllM.nW
    rw [hn.2]
...
example (h : BALWCutExp 3) (hE : STLocalEntrygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2))
    (hA : LWAvgLawgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hM : STLmaxgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2))
    (hK : STLKgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hD : STDecaygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) :=
  h le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2)
    (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) hE hA hM hK hD
...
example (h : BAGraphPrecJoin 3) (hE : STLocalEntrygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (P : BAPGraph (Fin 2)) (hN : P.g.Normal)
    (hn : P.g.nM = 0) :=
  h le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2)
    (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) hE P hN hn
...
example (st : BAPGraph (Fin 2) → Option (List ((ℕ × ℕ) × BAPGraph (Fin 2)))) (Inv : BAPGraph (Fin 2) → Prop)
    (Φ : BAPGraph (Fin 2) → ℂ) : ExpandGSum st Inv Φ (fun _ => 1) :=
  expandG_sum st Inv Φ (fun _ => 1)
```
**Ports:** none (no RBM1D/RBM2D text is used; the proof of `ba_W_sub_one` is a copy of `t/T2387:RBM3D/Probe/T2387Pins.lean:287`, never merged).

**Evidence scripts** (verbatim; `eng.py` models counters `(n_S, n_W, n_A)`, atoms and molecules of BA graphs and the rules `B:361-405`):
```
$ SP: python3 family.py           # first-level GG children of (eq:ELW_term) at BA; counter deltas on the compiled parent baCtx
ELW all-circled root: ord 2 ; GG candidates: [('gg', 'al')]
first-level GG children: 47 ; family: #terms, ord range: {'T1': (1, 2, 2), 'T2a': (1, 3, 3), 'T2b': (1, 3, 3), 'T3A0': (2, 3, 4), 'T3A1': (2, 3, 4), 'T3B0': (4, 3, 4), 'T3B1': (4, 3, 4), 'T3C0': (16, 3, 6), 'T3C1': (16, 3, 6)}
T3C by (k, differentiated edge #), edges of f = [(0, ('xp', 'xp', 1)), (3, ('X', 'Y', -1))] : {('0', '0'): (8, 3, 6), ('0', '3'): (8, 3, 5), ('1', '0'): (8, 3, 6), ('1', '3'): (8, 3, 5)}
context parent baCtx (nS,nW,nA,ord) = (2, 0, 2, -2)
   T1 (dnS,dnW,dnA,dord): [(-2, 1, -1, 2)]
   T2a (dnS,dnW,dnA,dord): [(-1, 1, 0, 1)]
   T2b (dnS,dnW,dnA,dord): [(-1, 1, 0, 1)]
   T3A0 (dnS,dnW,dnA,dord): [(0, 1, 0, 2), (1, 1, 1, 1)]
   T3A1 (dnS,dnW,dnA,dord): [(0, 2, 1, 2), (1, 2, 2, 1)]
   T3B0 (dnS,dnW,dnA,dord): [(-1, 1, -1, 3), (0, 1, 0, 2), (1, 1, 1, 1)]
   T3B1 (dnS,dnW,dnA,dord): [(-1, 2, 0, 3), (0, 2, 1, 2), (1, 2, 2, 1)]
$ SP: python3 pointwise.py   # (uses g5.py) terms at x != y that miss the pointwise target ord >= 5 by GG in depth 3, and under the corrected target ord >= 5 - 2*1[x~y]
x != y: normal terms 160 ; not reaching ord >= 5 by GG within depth 3: 28 ; of which x,y in one atom: 28 ; by (ord, same atom): {(4, True): 21, (3, True): 6, (2, True): 1}
terms failing the corrected target within depth 3: 0
$ SP: python3 tree5.py            # strategy S*: GG at a vertex with atom(y') != atom(y); leaf properties n_M <= 1, n_W >= 2, attached >= 2
x!=y case 1  : normal terms 32, already leaves 32, expanded 0, failing 0, total leaves 32, max depth 0, min margin ord-target 99, leaf-property violations {}
x!=y case 2  : normal terms 32, already leaves 31, expanded 1, failing 0, total leaves 78, max depth 1, min margin ord-target 0, leaf-property violations {}
x!=y case 3  : normal terms 32, already leaves 31, expanded 1, failing 0, total leaves 78, max depth 1, min margin ord-target 0, leaf-property violations {}
x!=y case 4  : normal terms 32, already leaves 26, expanded 6, failing 0, total leaves 1288, max depth 2, min margin ord-target 0, leaf-property violations {}
x!=y case 4b : normal terms 32, already leaves 32, expanded 0, failing 0, total leaves 32, max depth 0, min margin ord-target 99, leaf-property violations {}
x=y  case 1  : normal terms 32, already leaves 32, expanded 0, failing 0, total leaves 32, max depth 0, min margin ord-target 99, leaf-property violations {}
x=y  case 2  : normal terms 32, already leaves 32, expanded 0, failing 0, total leaves 32, max depth 0, min margin ord-target 99, leaf-property violations {}
x=y  case 3  : normal terms 32, already leaves 32, expanded 0, failing 0, total leaves 32, max depth 0, min margin ord-target 99, leaf-property violations {}
x=y  case 4  : normal terms 32, already leaves 31, expanded 1, failing 0, total leaves 78, max depth 1, min margin ord-target 0, leaf-property violations {}
x=y  case 4b : normal terms 32, already leaves 32, expanded 0, failing 0, total leaves 32, max depth 0, min margin ord-target 99, leaf-property violations {}
{'terms': 320, 'exp': 9, 'leaves': 1714, 'bad': 0}
$ SP: python3 parents.py          # the 9 expanded parents
x!=y case 2  : ord 4, target 5, (nS,nW,nA)=(4,2,2), M-edges=1, GG at vertex A, children 47, below target 0 -> second round at 0 vertex(es), leaves 47, depth<=2, min child margin 0
x!=y case 3  : ord 4, target 5, (nS,nW,nA)=(4,2,2), M-edges=1, GG at vertex A, children 47, below target 0 -> second round at 0 vertex(es), leaves 47, depth<=2, min child margin 0
x!=y case 4  : ord 3, target 5, (nS,nW,nA)=(5,2,3), M-edges=0, GG at vertex A, children 63, below target 14 -> second round at 1 vertex(es), leaves 1027, depth<=2, min child margin -1
x!=y case 4  : ord 2, target 3, (nS,nW,nA)=(4,2,3), M-edges=1, GG at vertex A, children 47, below target 0 -> second round at 0 vertex(es), leaves 47, depth<=2, min child margin 0
x!=y case 4  : ord 4, target 5, (nS,nW,nA)=(4,2,2), M-edges=1, GG at vertex A, children 47, below target 0 -> second round at 0 vertex(es), leaves 47, depth<=2, min child margin 0
x!=y case 4  : ord 4, target 5, (nS,nW,nA)=(4,2,2), M-edges=1, GG at vertex A, children 47, below target 0 -> second round at 0 vertex(es), leaves 47, depth<=2, min child margin 0
x!=y case 4  : ord 4, target 5, (nS,nW,nA)=(4,2,2), M-edges=1, GG at vertex B, children 47, below target 0 -> second round at 0 vertex(es), leaves 47, depth<=2, min child margin 0
x!=y case 4  : ord 4, target 5, (nS,nW,nA)=(4,2,2), M-edges=1, GG at vertex B, children 47, below target 0 -> second round at 0 vertex(es), leaves 47, depth<=2, min child margin 0
x=y case 4  : ord 2, target 3, (nS,nW,nA)=(4,2,3), M-edges=1, GG at vertex A, children 47, below target 0 -> second round at 0 vertex(es), leaves 47, depth<=2, min child margin 0
leaves of the 9 expanded parents 1403
$ SP: python3 lemma_final.py      # GGGamma order-change lemma (H1-H3) and its failure without H2, H3
GG order-change lemma: random parents (4 seeds) with atom(v) internal and meeting only the pair, atom(v),atom(y'),atom(y) distinct, atom(y') or atom(y) internal: 14331
  T1 Delta ord min/max (2, 2)
  T2a Delta ord min/max (1, 1)
  T2b Delta ord min/max (1, 1)
  T3A Delta ord min/max (1, 2)
  T3B Delta ord min/max (1, 3)
  T3C Delta ord min/max (1, 4)
without the atom hypotheses: 19414 random parents of the pair only; children with Delta ord <= 0 by family: {'T1': 9491, 'T3A': 3875}
$ SP: python3 elw_summary.py      # (eq:ELW_term) at BA, pure graph route, all rules
ELW root: 8 normal terms; candidates: weight, lanlw tail (any edge, internal or external tail), lanlw head (any edge), GG; depth <= 5
term 0: ord=2 target=5 x~y=False min depth=None (40.2s)
term 1: ord=1 target=3 x~y=True min depth=2 (0.0s)
term 2: ord=3 target=5 x~y=False min depth=None (2.8s)
term 3: ord=2 target=3 x~y=True min depth=1 (0.0s)
term 4: ord=3 target=5 x~y=False min depth=None (0.9s)
term 5: ord=2 target=3 x~y=True min depth=1 (0.0s)
term 6: ord=2 target=3 x~y=True min depth=1 (0.0s)
term 7: ord=1 target=3 x~y=True min depth=2 (0.0s)
$ SP: python3 regen.py            # the stuck family T3C-G: one lanlw step
(b) T3C-G: (nS,nW,nA)= (5, 2, 3) ord 3 target 5 x~y False
candidates (kind, edge, vertex): [('lw', 0, 'xp'), ('la', 3, 'de'), ('la', 4, 'de'), ('la', 1, 'X'), ('la', 2, 'X'), ('lh', 1, 'al'), ('lh', 2, 'ga')]
lanlw tail at the edge (x->alpha): 34 children; Delta ord histogram {0: 3, 1: 10, 2: 12, 3: 7, 4: 2}
  LA2e2 (nS,nW,nA)= (5, 3, 4) circled solid: [('de', 'Y', 1), ('de', 'Y', -1), ('n3', 'al', 1), ('n3', 'ga', -1)] dot: [('X', 'n2'), ('al', 'ga')] GG candidates: []
  LA2e2 (nS,nW,nA)= (3, 3, 3) circled solid: [('de', 'Y', 1), ('de', 'Y', -1)] dot: [('X', 'n2'), ('al', 'ga'), ('n3', 'al'), ('n3', 'ga')] GG candidates: []
  LA2e3 (nS,nW,nA)= (5, 3, 4) circled solid: [('X', 'ga', -1), ('de', 'Y', -1), ('n3', 'al', 1), ('de', 'n3', 1)] dot: [('X', 'n2'), ('al', 'ga'), ('n2', 'Y')] GG candidates: ['n3']
$ SP: python3 mc_gg.py 2 10       # Monte Carlo of the corrected GGGamma: d=1 L=3 W^d=2 t=1 g=0.7 z=0.2+0.5i, 1e6 samples
f=f1: E[LHS]=-0.00135+0.00871j  E[RHS corrected (W-1)=M+SW]=-0.00142+0.00872j  E[RHS printed S+=SW]=0.04323-0.02006j   |LHS-corr|=6.83e-05  |LHS-printed|=5.31e-02  MC err (LHS-RHS stddev/sqrt n)=1.0e-04
f=fb: E[LHS]=0.00050+0.00843j  E[RHS corrected (W-1)=M+SW]=0.00046+0.00844j  E[RHS printed S+=SW]=0.01813+0.00323j   |LHS-corr|=4.64e-05  |LHS-printed|=1.84e-02  MC err (LHS-RHS stddev/sqrt n)=4.2e-05
$ SP: python3 kern.py ; python3 twist.py ; python3 crude.py
kernel omega = (1 - t M+_B)^-1, M+_B = M^B o M^B (Hadamard square); (W-1) block kernel K~ = omega - 1; row sums, spectral radius, offset-independence
g=0.015625  rho(tM+B)=0.4996  max_a sum_c |omega_ac|=0.6673  max_a sum_c |K~_ac|=0.3333  max_a sum_c |M_ac|=1.0988  sum_c|M_ac|^2 = 1.0000 (Ward: Im m/(Im m + 0) -> 1.0 at eta=0)
g=1         rho(tM+B)=0.4469  max_a sum_c |omega_ac|=0.9760  max_a sum_c |K~_ac|=0.3544  max_a sum_c |M_ac|=4.3220  sum_c|M_ac|^2 = 1.0000 (Ward: Im m/(Im m + 0) -> 1.0 at eta=0)
g=10        rho(tM+B)=0.4994  max_a sum_c |omega_ac|=0.9902  max_a sum_c |K~_ac|=0.3503  max_a sum_c |M_ac|=4.0534  sum_c|M_ac|^2 = 1.0000 (Ward: Im m/(Im m + 0) -> 1.0 at eta=0)
d=3 L=3 E=0.0 t=0.5: deterministic parts of the 2-loops (units W^-d): standard K(a,c)=sum_a' R_aa' |M_a'c|^2 and mixed (block-jump) Kt(a;c1,c2)=sum_a' R_aa' M_a'c1 conj(M_a'c2), R=(1-t M+_B)^-1
g=0.015625  rho(tM+B)=0.4996  max_c K_std(a,c)=0.6660-0.0000j  max_(c1!=c2) |Kt|=0.0104 at (0, 9)  ratio=0.016+0.000j;  sum_(c1!=c2)|M_c1c2||Kt| = 0.0020 vs diagonal part sum_c |m| K_std = 0.6668-0.0000j  (off/diag = 0.003+0.000j)
g=1         rho(tM+B)=0.4469  max_c K_std(a,c)=0.3784-0.0018j  max_(c1!=c2) |Kt|=0.0865 at (0, 24)  ratio=0.228+0.001j;  sum_(c1!=c2)|M_c1c2||Kt| = 2.0176 vs diagonal part sum_c |m| K_std = 0.4742+0.0036j  (off/diag = 4.255-0.032j)
g=10        rho(tM+B)=0.4994  max_c K_std(a,c)=0.3601-0.0002j  max_(c1!=c2) |Kt|=0.0900 at (0, 5)  ratio=0.250+0.000j;  sum_(c1!=c2)|M_c1c2||Kt| = 1.7368 vs diagonal part sum_c |m| K_std = 0.4447+0.0004j  (off/diag = 3.905-0.004j)
crude bound of the twisted family (b) with Ward: |tr| * |L~| * eta^-1 <= eta^-1 B^2 against the target eta^-1 B^(5/2); crude/target = B^(-1/2), B = W^-d B_{t,0}
g=0.015625  B_t0=2.0731 W=    27: B=W^-d B_t0=1.053e-04  crude/target = B^-1/2 = 97.4   (= W^(d/2) B_t0^(-1/2); W^(d/2) = 140.3)
g=0.015625  B_t0=2.0731 W= 10000: B=W^-d B_t0=2.073e-12  crude/target = B^-1/2 = 694528.5   (= W^(d/2) B_t0^(-1/2); W^(d/2) = 1000000.0)
g=1         B_t0=0.7407 W=    27: B=W^-d B_t0=3.763e-05  crude/target = B^-1/2 = 163.0   (= W^(d/2) B_t0^(-1/2); W^(d/2) = 140.3)
g=1         B_t0=0.7407 W= 10000: B=W^-d B_t0=7.407e-13  crude/target = B^-1/2 = 1161895.0   (= W^(d/2) B_t0^(-1/2); W^(d/2) = 1000000.0)
g=10        B_t0=0.0840 W=    27: B=W^-d B_t0=4.269e-06  crude/target = B^-1/2 = 484.0   (= W^(d/2) B_t0^(-1/2); W^(d/2) = 140.3)
g=10        B_t0=0.0840 W= 10000: B=W^-d B_t0=8.402e-14  crude/target = B^-1/2 = 3449828.4   (= W^(d/2) B_t0^(-1/2); W^(d/2) = 1000000.0)
```

**Narrative.**
- Read: the ticket; section (a); `docs/supervisor/2026-10-10-2149.md`; `docs/reports/T2387-design.md`; `docs/reports/T2325-portmap.md` (rows 14-16, lines 43-46); `t/T2387:RBM3D/Probe/T2387Pins.lean:240-399`; `paper/tex/B_graphical_lemmas.tex:1-125, 286-420`; `7_8_light_weight.tex:296-360` and a `grep` of `:1792-2105`; the Lean files `Chain/LWGen.lean`, `Chain/Carrier.lean:40-200`, `BA/LWPinsBA.lean`, `BA/FlowPins.lean:300-400`, `Graph/LWExpTerm.lean:1-120`, `LWExpTerm2.lean:1-140`, `LWExpTerm3.lean:1-110`, `LWExpTerm4.lean:1-130`, `LWExpTerm5.lean:1-377, 560-739`, `LWExpTerm6.lean:1-120`, `LWExpCert.lean`, `LWExpCertB.lean:1-100`, `BAVocab.lean:1-330, 1170-1260`, `BAExpandWOrd.lean:1-140`, `Loop/GLoopFlow.lean:60-125`, `BA/GreenSchur.lean:80-125`. `LWExpSim.lean:1080-1150` was not read: its names `partitionSim`, `childrenSim` are taken from T2325 row 16.
- Section (a) was not edited; its rows 2, 6 and 11 agree with the engine and the Monte Carlo of this stage (rows 3, 5, 7 were not re-run), so there is no (a′).
- Engine: an independent implementation of the BA rules (`GGGamma` with D402, `lanlw` tail and head, `lweight`, the `G = Ǧ + M` split) at the level of counters and atoms. It reproduces the finding of (a) that the pointwise failures all have `x ~ y`: 28 of 160 normal terms at `x ≠ y` miss the pointwise target, none misses the corrected one.
- New in this stage: the context lemma for `GGGamma` (design §3.3); the closure table with leaf properties (§3.4); the stall of the pure graph route for `(eq:ELW_term)` (§8); the Monte Carlo of the full `GGGamma` identity for two `f` (§4); the offset-twisted loops and the compiled tie identity `twTie` (§1.2, §2, §8).
- Probe: 399 lines, 36 declarations on the three standard axioms, `lake build` and `lake env lean` clean, no forbidden token, no name clash; commits `2e23b9f`, `e32530a`, `5f96301`, `5c62eb7`, `fdc8c57`, `2257f54` (the only file of the diff).
- Decisions: W2 no; W3 C; STOP at one missing step (design §8), one question to Jun. The row table is conditional on that answer.
- Not done: no Lean proof of the context lemma (owed by L2c2); the family pins of L4a, L4b, L4c are text; `Kt` of `BATwistLaw` is the expected ladder, not derived.
- Length of this report: 290 lines (limit 300).

## (c) Verified names

- Mathlib, present (the probe builds): `Finset.card_pos`, `Finset.mem_filter`, `Finset.mem_univ`, `Finset.sum_eq_single`, `Finset.sum_congr`, `Finset.mul_sum`, `Matrix.mul_apply`, `Matrix.one_apply_ne`, `Ring.inverse_mul_cancel`, `Ring.mul_inverse_cancel`, `Equiv.symm_apply_apply`, `Equiv.apply_symm_apply`, `Equiv.injective`, `Prod.ext`, `mul_le_mul_of_nonneg_left`, `sub_eq_iff_eq_add`, `sub_mul`, `one_mul`.
- Tactics: `push Not` (present); `push_neg`, `if_pos`, `if_neg` are deprecated in this Mathlib (warnings of the first builds: "Prefer using `push Not`", "`if_pos` has been deprecated"; `↓reduceIte` is used instead).
- Project names used, present by `grep` and by the build: `STBctl_ge` (`Induction/ScaleFacts.lean:126`), `expandG_sum`, `ExpandGSum` (`Graph/LWExpTerm5.lean:234, 199`), `BAMfine_eq` (`BA/GreenSchur.lean:93`), `BAMB`, `BAmF`, `BAflowLam0`, `BAflowEs`, `BAPsi_isHermitian`, `isUnit_sub_smul_of_isHermitian`, `card_adj`, `Adj`, `PsiB`, `baW_isUnit`, `BAlwW`, `BAlwMp`, `BAlwS`, `BAlwData`, `BASelf`, `PF`, `splitEquiv`, `split`, `FlowFM.GM`, `PrecL`, `baPin`, `bandPin`, `LWcutg`, `LWCutExp`.
- Verified absent: none needed.

## (d) Open issues and paper-delta candidates

1. **The missing step** (design §8, family `T3C-Ḡ`): one question to Jun, forms (R1) a law for loops with an off-diagonal block insertion, (R2) an expansion of `ǦMǦ` at an atom. No row of L4a, L4b can be fixed before the answer.
2. L2c2 must prove the context lemma (design §3.3) with the counters of the three `GGGamma` sums; L4e-C is priced without it.
3. `BARCand` (design §4) is a proposed name, not defined. The pins `BAG5Identity`, `BAG5Expand`, `BATwistLaw` are `Prop`-valued with no proof.
4. The scripts are not in the repository: the output in (b) is the record. The engine is a model of counters, atoms and molecules, not of values (design §8, limits).
5. Row estimates (design §7) use T2387's ratios; L4e-C, the splits and the unpriced input of §8 are estimates.
6. Paper-delta candidates (temporary tags, texts in design §8): `T2398a` pointwise `(eq:sizeGammamu_E)` is false at BA, corrected target `5 − 2·1[x ~ y]`; `T2398b` `(eq:GGraisesord)` needs three atom conditions (extends `T2387b`); `T2398c` the atomic correspondence (`B:320-323`) fails for the rules; `T2398d` `B:118` omits the offset-twisted loops; `T2398e` `S^{(B)} = I` gives `a₂ = a₁` and the kernel `(1 − tM⁺_B)⁻¹`; `T2398f` D402 checked in expectation (evidence for `T2161a`, `T2387a`).
