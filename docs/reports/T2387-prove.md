Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct 10 12:46:07 UTC 2026 (`date -u`)

T2387 is a design ticket (report + probe). Its mathematical content is the exponent bookkeeping the stage-L pins and the cutoff rely on. No new external hypothesis is introduced: the unmerged inputs (stage E `Θ_BA` profile, T2386 `Chain/Step2Gen`) enter only as local hypotheses. Sources: paper `B_graphical_lemmas.tex` (cited `B:line`), `7_8_light_weight.tex` (`7:line`), `RBM3D/Graph/LWLvl1.lean:3981`, `RBM3D/Graph/ScalingOrder.lean`, `RBM3D/Graph/BAVocab.lean`, `RBM3D/BA/KKernel.lean:352`.

### (i) Exponent table
| quantity | value | constraint it must satisfy | slack | source |
|---|---|---|---|---|
| `ord(Γ)` (BA) | `n_S + 2(n_W - n_A)`; `Counters.nV` holds `n_A` | none (integer) | merged BA graphs: `baGcxy` 1, `baGcxx` -1, `baGGLhs` 0, `baGGT1` 0, `baLWT1` 0 | `B:353`, `ScalingOrder.lean:65`, `BAVocab.lean:145` |
| `lanlw` step | `n_S+1, n_W+1, n_A+1`, so `ord+1` | `ord Γ ≤ ordG Δ` for all terms | tight (`T2315_D` term) | `BAExpandWOrd.lean:21-24, 781` |
| target orders of `lem:LWterm_EXP` | `ord(Γ_μ,xy) ≥ 4·1[x=y] + 5·1[x≠y]`, i.e. `(W^{-d}B_{t,0})^{2}` and `^{5/2}` | `Ψ_t = (W^{-d}B_{t,0})^{1/2}`, `Γ ≺ η^{-1} Ψ^{ord}` | 0 at `x≠y` | `B:68-77, 92` |
| count `x = y` in `I_42` (step the paper does not write) | `W^{-2d}·W^d = W^{-d}` pairs | `W^{-d} ≤ (W^{-d}B_{t,0})^{1/2}` iff `B_{t,0} ≥ W^{-d}`; `B_{t,0} ≥ (L^d|1-t|)^{-1} ≥ L^{-d}` for `|1-t| ≤ 1`, so `L ≤ W` suffices | instance `5.08e-5 ≤ 8.46e-3` | `B:68-77`, `Defs/Params.lean:36` |
| `K0` (`L^d ≤ W^{K0}`) | 1 | `L^d ≤ W^{K0}` | **0** at `(L,W) = (3,27)`, `d = 3`; `K0 = 1` forces `L^d ≤ W`, so `L ≥ 3` needs `W ≥ 27` at `d = 3` | `LWLvl1.lean:3990` |
| `c` (`Ψ ≤ W^{-c}`) | 1/4 | `0 < c`; `Ψ_t ≤ W^{-c}` iff `B_{t,0} ≤ W^{d-2c}` | `B_{t,0} = 1.4074 ≤ 27^{2.5}` | `LWLvl1.lean:3991` |
| lower window `W^{-d/2} ≤ Ψ_t` | `Ψ_t = (W^{-d}B_{t,0})^{1/2}` | iff `B_{t,0} ≥ 1` | `B_{t,0} = 1.4074` (needs `g² + |1-t| ≤ 1`) | `LWLvl1.lean:3991`, `Defs/Params.lean:36` |
| `ε₀` (`Ψ ≤ W^{-ε₀}`) | any `0 < ε₀ ≤ 1.448` at the instance | `STLWT`/`LWAssmExp` window | `ε₀ = c = 1/4`, slack 1.198 | `Step2Defs.lean:421-431`, `LWPins.lean:283-286` |
| `D` (error exponent) | 10 | `D > 0` | n/a | `LWLvl1.lean:3981` |
| `lvl1Cutoff c K0 d D G` | `⌈(D + K0 n_M + d (n_A - n_W)⁺)/c⌉`: `baGcxy` 40, `baGGT1` 40, `baGcxx` 52, `baGGLhs` 56, `baLWT1` 56, `p2` BA reading 72 | smallest `K` with `cK ≥ D + K0 n_M + d(n_V - n_W)⁺`; needs `n_M(Q) ≤ n_M(G)`, `(n_A-n_W)(Q) ≤ (n_A-n_W)(G)` | a graph `⟨80,4,6,1⟩` has `ord 76 ≥ 72` and `log_W size = -13 ≤ -10` (slack 3) | `LWLvl1.lean:3981-3994, 4355-4370` |
| `p` (moment) | `p ∈ 2ℕ`, `p = 2` merged (`p2Graph`) | Markov: `pδ ≥ D` for each `δ > 0`; `ord(fxyPowGraph p) = p` (`n_S=3p, n_W=p, n_A=2p, n_M=p`); cutoff `16p+4D` | `p=2`: 72; `p=4`: 104 | `7:72-92`, `LocalRegular.lean:33, 1978` |
| property (6) | `ord ≥ 2p` all, `ord ≥ 3p` far (`x≠y`) | replaces the paper's `ord + n_dv + n_lw` monotone step (false, DECISIONS §47); merged route is the merge cost `scost` over `LGraph` | initial values `Φ^all = 2p`, `Φ^far = 3p`; `p2Graph` has ord 2 < `2p` = 4 before expansion | `LocalRegular6a.lean:24, 86-87`, `B:200-278, 272-275` |
| `n_dv`, `n_lw` | 0 in every merged BA counters tuple | not part of `ord`; only the (replaced) paper bookkeeping uses them | no BA row needs them if (6) is taken through `scost` at atoms (open design point, see verdict LD3) | `ScalingOrder.lean:59-61`, `BAVocab.lean:1237` |
| `ε₁` (atom radius) | `ε₁ ∈ (0, 1/10)`: atoms `\|[x]-[y]\| ≤ (log W)^{1+ε₁}`; aux waved edge `W(log W)^{1+2ε₁}` | `1 + 2ε₁ < 3/2` (the band scale of `7:95`); `ℓ ≤ (log W)^{10} ℓ_t` | `1 + 2ε₁ < 1.2`, slack > 0.3 | `B:317, 448` |
| `ord(G) - ord(G^aux)` (exponent of `Ψ` in `(G_by_auxG_BA)`) | `≥ 0` (derived here, not in the paper): per molecule, `n_W^{within} ≥ k_i - 1` (waved-connected atoms), kept non-centers `r_i - 1`, discarded internal atoms `k_i - r_i`; `2(n_W^{within} - (r_i-1)) - 2(k_i - r_i) ≥ 0`, plus one per removed solid edge | molecule = waved-connected atoms (`B:176, 298`) | 0 iff the waved graph of each molecule is a tree on its atoms and no solid edge is removed | `B:486-489` |
| `1 - t` lower bound for the `T`-bound | paper `7:88`: `1 - t > λ²/L²`, as in the Lean moment statement (`LWPins.lean:349`); Lean `LWtermEXP` (`LWPins.lean:311-318`): `λ²/L^d ≤ 1-t`; `LWtermExp` has neither | the sizes where it fails are outside the index set | instance: `1-t = 0.5` vs `λ²/L² = 0.0278`, `λ²/L^d = 0.0093` | `7:88`, `LWPins.lean:318, 349` |
| `ℓ_t` and the `ℓ` cap | `ℓ_t = min(max(g/√\|1-t\|, 1), L) = 1` at the instance | `0 ≤ ℓ ≤ (log W)^{10} ℓ_t` | cap `1.51e5` | `Defs/Params.lean:32`, `LWPins.lean:284-286` |
| row 10 hypothesis `D.M x y = if x = y then m else 0` | **fails at BA data** with `g > 0` | a BA datum with `Σ_{b~a} \|M_ab\|² ≥ (κ(1-\|m\|²))²/(8 d g²) > 0` has a neighbour with `M_ab ≠ 0` | instance: `Σ = 0.1367 ≥ 3.4e-4`, `min_{b~a} \|M_ab\| = 0.151` | `BA/KKernel.lean:352`, `BA/MFixedPoint.lean:190, 432` |
| `κ ≤ Im m` and `\|m\| < 1` | `Im m = 0.7404 ≥ κ = 0.1`, `\|m\| = 0.7406` | `BAReal d L g κ E m` | slack 0.640 (`Im m - κ`) | `BA/MFixedPoint.lean:432` |

Remarks on rows: the windows `W^{-d/2} ≤ Ψ_t ≤ W^{-c}` and `L^d ≤ W^{K0}` are hypotheses of `lvl1_size_le` (not derived); `B_{t,0}` is the merged `Bparam` with `g = lam`, so whether the BA profile of stage E agrees with it is not checked here (flag for LD2/LD5). `T2386` (`Chain/Step2Gen`) is not on `main` (`ls RBM3D/Chain` lists only `Carrier.lean`).

### (ii) One concrete nondegenerate instance (`d = 3`)
Data: `d = 3`, `L = 3`, `W = 27` (`N = (WL)^d` block sizes nonempty), `g = lam = 1/2`, `t = 1/2`, `κ = 0.1`, `E = 0`, `c = 1/4`, `K0 = 1`, `D = 10`, `p = 2`. `Ψ_t = (W^{-3} B_{t,0})^{1/2}` with `B_{t,0} = (g² + |1-t|)^{-1} + (L^d |1-t|)^{-1}`. Block datum: `m` solves `m = L^{-d} tr (g Ψ^B - E - m)^{-1}` on `Z_3^3` (`Ψ^B` = adjacency of `Adj`, `zdistD = 1`; degree 6), by fixed-point iteration, `M^{(B)} = (gΨ^B - E - m)^{-1}`.

Command and output (pure arithmetic, no Lean):
`cd <scratchpad>/T2387 && python3 pre.py` (script `<scratchpad>/T2387/pre.py`)
```
baGcxy           nS=1 nW=0 nA=0 nM=0 ord=1 cutoff=40
baGcxx           nS=1 nW=0 nA=1 nM=0 ord=-1 cutoff=52
baGGLhs          nS=2 nW=0 nA=1 nM=1 ord=0 cutoff=56
baGGT1           nS=0 nW=1 nA=1 nM=0 ord=0 cutoff=40
baLWT1           nS=2 nW=1 nA=2 nM=1 ord=0 cutoff=56
p2(BA reading)   nS=6 nW=2 nA=4 nM=2 ord=2 cutoff=72
fxyPow p=2: ord=2 cutoff=72 need(6): all>=2p=4 far>=3p=6
fxyPow p=4: ord=4 cutoff=104 need(6): all>=2p=8 far>=3p=12
fxyPow p=6: ord=6 cutoff=136 need(6): all>=2p=12 far>=3p=18
L^d = 27  W^K0 = 27  L^d<=W^K0: True
window W^-d/2=0.00713 <= Psi=0.00846 <= W^-c=0.43869: True;  B_t0=1.4074>=1:True; B>=W^-d: True
eps0_max with Psi<=W^-eps0: 1.4481543978636946
1-t>=g^2/L^d: True   1-t>lam^2/L^2: True
ell_t= 1  (log W)^10*ell_t= 151236.6583654054
log_W size = -13  <= -D: True  ord= 76  cutoff(p2)= 72
x=y counting: W^-d = 5.080526342529086e-05  <= (W^-d B)^(1/2) = 0.008455986286651545 True
ord needed: 4,5 -> exponents of (W^-d B): 2.0 2.5
m = (-0.01656926801338585+0.7403974664054362j)  |m|= 0.7405828440506089  fixed-pt residual 1.1102230246251565e-16
Im m >= kappa=0.1: True
deg = 6  sum_{b~a}|M_ab|^2 = 0.1366559140561304  >= bound 0.0003398095141903298 : True  min |M_ab| over b~a: 0.15091714838288484
scalar-M hypothesis (M x y = if x=y then m else 0) holds? offdiag max |M_ab| = 0.15091714838288514  diag M_aa = (-0.01656926801338581+0.740397466405436j)  m = (-0.01656926801338585+0.7403974664054362j)
```
At this instance every hypothesis of the pins holds at once: the cutoff lemma (`L^d = 27 ≤ W^1`, window nonempty `[0.00713, 0.43869] ∋ 0.00846`, `D = 10`, counters inside the cutoff), the `LWtermExp` window (`ε₀ = 1/4`, `0 ≤ ℓ ≤ 1.5e5`, `D > 0`), the `LWtermEXP` side condition (`1-t = 0.5 ≥ λ²/L^d`), and the BA datum (`κ ≤ Im m`). No `N = 0`, empty index, or collapsed window; `L = 3 ≥ 3`, `W = 27`. The merged T2325 probe instance used `L = 1`, `K0 = 0` (`git show t/T2325:RBM3D/Probe/T2325BAGen.lean`, lines 83-86) and the merged BA `lanlw_val` instances use `W = 1`, `g₀ = 0` (`BAExpandW.lean:34`), where `M` is scalar and row 10 is invisible; the stage-L probe must use `g > 0`, `L ≥ 3`, `W ≥ 27`.

### Verdicts
- LD1 (route per family, measured): PASS. Row 10 finding confirmed numerically: the scalar-`M` hypothesis fails at BA data with `g > 0` (off-diagonal `|M_ab| = 0.151`). Under C1 a G form of row 10 must read the atom/`M`-dotted structure instead of that hypothesis; no exponent obstruction.
- LD2 (outputs pinned at BA): PASS at the mathematics level, provisional: `T2386` not merged. Needs `κ ≤ Im m` (slack 0.64 here) and the `Θ_BA` profile of stage E for `B_{t,r}`; the table uses the merged `Bparam`, so the BA-profile agreement is a gap to report, not to pin around.
- LD3 (paper status): PASS (the question is a reading task). Mathematical findings: (1) `B:416` takes properties (1)-(6) over verbatim, but the paper's (6) step `ord + n_dv + n_lw` is false (DECISIONS §47), so BA inherits the gap; the merged route (`scost`, `LocalRegular6a.lean`) is on `LGraph` and needs an atomic twin; (2) `B:72-77` omits the `x = y` count (`B_{t,0} ≥ W^{-d}`); (3) `(G_by_auxG_BA)` has no written exponent argument, a nonnegative exponent is derived above; (4) `B:118` ("omit") leaves the whole BA `GG`-expansion (`GGGamma`) output list and its order counts to the reader, no argument in the paper.
- LD4 (certificate cost): PASS (no exponent at stake; the cutoff table above is the input: BA cutoffs 40-72 for `D = 10`).
- LD5 (dependencies): PASS. The `κ`, `Θ_BA` profile and `K` kernel facts enter as local hypotheses (BA datum computed here for `d = 3`).
- LD6 (deliverables / probe instance): PASS. The instance above has every hypothesis simultaneously; the probe must not reuse the `L = 1`, `K0 = 0`, `W = 1`, `g₀ = 0` merged instances.
- LD7 (flag and count): PASS (no number in the table depends on it).

## (a′) Preflight corrections — Sat Oct 10 16:21:43 UTC 2026 (`date -u`)
- Row 15 (the exponent of `Ψ` in `(G_by_auxG_BA)`): by counting from `(eq:ordG_BA)` (`B:353`) and `(eq:ordGaux_BAM)` (`B:486`), `ord G - ord G^aux = n_S^{within} + 2 Σ_i [e_i + (k_i^{ext} - r_i^{ext})]`, `e_i = n_W^{(i)} - (k_i - 1) ≥ 0` the waved edges of molecule `i` beyond a spanning tree of its `k_i` atoms, `r_i` the retained atoms. It is 0 iff no solid edge lies inside a molecule, every molecule is a waved tree on its atoms and every external atom is retained; (a) omits the last condition. Verdict unchanged.
- LD2 verdict: `B_{t,K}` is one definition for both models (`1_2:1107-1110`, `Defs/Params.lean:36`), so the BA profile of the table is the merged `Bparam` and no stage-E producer is needed for it; the BA input is the `Θ_BA` decay of stage P (`baProp5s_holds`, `BA/Prop5Short.lean:667`). The "gap to report" is closed; verdict unchanged.

## (b) Script output — Sat Oct 10 16:21:43 UTC 2026 (`date -u`)
`$WT` = `/Users/junyin/Lean_proof/RBM3D-wt/T2387`, `$SP` = scratchpad `T2387/` (scripts; not in the repository). Classes and densities are readings of statement tokens, not compiled. `[Bk]` is cited in the design report.
```
$ [B0] cd $WT; date -u; git log --oneline -3; git diff --stat main...t/T2387; wc -l RBM3D/Probe/T2387Pins.lean
Sat Oct 10 16:17:52 UTC 2026
fe433f2 T2387: probe: STMainIndG citation at the branch base (BA/FlowPins.lean:434) (never merged)
5c3245e T2387: probe: docstring of the GG order example names the external y, y' (never merged)
97550e0 T2387: probe: BA instances of the L pins, GG order example, linter clean (never merged)
 RBM3D/Probe/T2387Pins.lean | 399 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 399 insertions(+)
     399 RBM3D/Probe/T2387Pins.lean
$ [B1] lake build RBM3D.Probe.T2387Pins 2>&1 | tail -2; lake env lean RBM3D/Probe/T2387Pins.lean; echo "lake env lean exit $?"
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3976 jobs).
lake env lean exit 0
$ [B2] lake env lean $SP/s_axioms_check.lean | sed -E "s/^'[^']*' //" | sort | uniq -c; grep -cE 'sorry|admit|^axiom |native_decide' RBM3D/Probe/T2387Pins.lean
  52 depends on axioms: [propext, Classical.choice, Quot.sound]
forbidden tokens (sorry/admit/axiom/native_decide) in the probe: 0
$ [B3] sed -n '129,140p;343,347p' RBM3D/Probe/T2387Pins.lean; grep -n '^def <pin names>\|^abbrev BA' RBM3D/Probe/T2387Pins.lean   (name@line)
def LWtermEXPG (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
        STLocalEntrygL (mk sz z) (law sz) t → LWAvgLawgL (mk sz z) (law sz) t → STLmaxgL (mk sz z) (law sz) t →
        STLKgL (mk sz z) (law sz) t → STDecaygL (mk sz z) (law sz) t →
        PrecL sz (law sz) (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) //
            sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n})
          (fun n p _ => ‖∫ ω, LWEg (mk sz z) n (t n) p.1.1 p.1.2 ω ∂(law sz)‖)
          (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))
/-- **`GGGamma`** (corrected, D402): `𝔼[BAGGGammaL] = 𝔼[BAGGGammaR]` over `PF d L W 0` (owed: BA-L2c). -/
def BAGGGamma (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), BASelf d L g0 (E : ℂ) m → 0 ≤ t → t < 1 →
    ∀ (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) (x y y' : Idx d L W),
      ∫ ω, BAGGGammaL d L W g0 E t m P x y y' ω ∂(PF d L W 0) = ∫ ω, BAGGGammaR d L W g0 E t m P x y y' ω ∂(PF d L W 0)
-- pins and observables (name@line): LWcutg@49 LWEg@54 STEGtg@58 LWAvgLawgL@64 LWAssmgL@75 LWAssmExpgL@88 STLWassmgL@93 LWtermG@100 LWtermExpG@114 STLWBG@143 STLWTG@156 STEMn2ExpG@175 bandPin@203 baPin@205
-- BA readings: BALWterm@237 BALWtermExp@238 BALWtermEXP@239 BASTLWB@240 BASTLWT@241 BASTEMn2Exp@242
$ [B4] sed -n '383,387p;390,394p' RBM3D/Probe/T2387Pins.lean; grep -n '^example' ...; grep -n 'theorem sz0_values\|theorem flow_sz0 ' $WT/RBM3D/{Defs/Sizes,BA/FlowPins}.lean
example (h : BALWtermEXP 3) (hE : STLocalEntrygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2))
    (hA : LWAvgLawgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hM : STLmaxgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2))
    (hK : STLKgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hD : STDecaygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) :=
  h le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2)
    (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) hE hA hM hK hD
example (h : BAGGGamma 3) (P : MvPolynomial (Bool × Idx 3 (sz0.L 0) (sz0.W 0) × Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
    (x y y' : Idx 3 (sz0.L 0) (sz0.W 0)) :=
  h (sz0.L 0) (sz0.W 0) (sz0.three_le_L 0) (BAflowLam0 sz0 zSeq 0) (BAflowEs sz0 zSeq 0) (1 / 2)
    (BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0) (BAflow_real _ _ _ _ sz0 zSeq flow_sz0 0).1 (by norm_num)
    (by norm_num) P x y y'
-- all examples (probe lines): 307 308 309 313 317 371 375 379 383 390; band recoveries (theorem band_*, *_iff): 18
267:theorem sz0_values : sz0.L 0 = 4 ∧ sz0.W 0 = 32 ∧ sz0.size 0 = 2097152 ∧ sz0.lam 0 = 1 / 64 := by
1235:theorem flow_sz0 : BAFlow sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq := by
$ [B5] python3 -I $SP/s_clash.py
new public declarations of the probe: 52
declarations elsewhere in RBM3D/ with the same short name: 3
  Graph/LWPins.lean:522  RBM.Gauss.LWInst.Ψ0
  Induction/Step2Defs.lean:982  RBM.Gauss.Step2DefsInst.Ψ0
  Induction/NQGood1.lean:1094  RBM.Ind.NQGood1Inst.ell0  (private)
same full name (clash): 0
$ [B6] python3 -I $SP/s_fam3.py $WT fam     # statement-token census of the 58 Graph files (columns R V St Sh Tc Tm: design §1.1)
file/family           lines   H+O     I |     R     V    St    Sh    Tc    Tm |  priv privR
F0 pins                1008   137   295 |   208     0    15     0    86   267 |     0     0
F1 vocab               3046   507   123 |   560  1493     0    44   319     0 |   784   672
F2 Stein               1983   243   190 |   292   154   523    64   361   156 |    19    19
F3 expansion ops       4800   447   279 |   467   373   101   439  2516   178 |     2     2
F4 symmetric forms     2326   300   146 |    29   235    34   525  1054     3 |     3     3
F5-8 lvl1              4462   309   260 |   115   880    18   500  2380     0 |   197   178
F9 locreg             11165  1262  1425 |  1784   845     0  3956  1893     0 |  2535   563
F10 GtoAG/size         3331   314   241 |  1080   902     0   137   657     0 |   464   421
F11 xi                 2856   246   225 |  1469   162   150   108    60   436 |  1117   840
F12 Anp                7157   758   570 |  3363  2466     0     0     0     0 |   240   240
F13 moment             6060   488   317 |  2473   921    80    58   229  1494 |  1616  1104
F14 engine/prov        2757   309   208 |    65   631    52   328  1164     0 |    26    26
F15 identity half       739   110    96 |   118   123     0    79   213     0 |   194    54
F16 cert/sim/sound     5007   529    90 |   395   539     0  3424    30     0 |  1482   392
F17 Psi                 813   117   146 |   550     0     0     0     0     0 |   177   177
F18 LW-14 terms        8265   682   380 |  2343   320   142  1137   506  2755 |  2174   747
F19 Markov             2347   181    91 |   973     0    52     4     0  1046 |   468   345
BA merged              4399   529   185 |   766  1429   208   459   304   519 |  1406  1196
TOTAL                 72521  7468  5267 | 17050 11473  1375 11262 11772  6854 | 12904  6979
$ [B7] python3 -I $SP/s_deps3.py $WT LWSizeClaim LWMoment AuxGraph2 LWTermHolds LWMomExp LWExpTerm LWExpTerm4 LWExpTerm6   # stage-directory names a file uses (word match)
LWSizeClaim   Propagator: Prop5Short PropSpin Theta_apply_add_right_of_three_le mul_Theta_of_three_le prop5Short_holds
LWMoment      Green: RangeCond eta_lower_of_rangeCond gaussIBP im_green_diag norm_green_apply_le_etaT stGbEXP_holds v3_premises_of_stFlow | Loop: blockMat etaT_eq_zt_im etaT_pos loopFine trace_Eblk | Propagator: sum_SBR_row
AuxGraph2     Green: stGbEXP_holds v3_premises_of_stFlow | Loop: blockMat etaT_eq_zt_im etaT_pos loopFine z0_im_pos
LWTermHolds   Green: stGbEXP_holds v3_premises_of_stFlow | Kernel: sfT_antitone sfT_nonneg sfT_zero sqrt_add_le_add_sqrt | Loop: etaT_pos z0_im_pos
LWMomExp      Evolution: ekTTk_holds | Kernel: PsiT_nonneg sfT_le_zero_mul sfT_nonneg sfT_zero_le_PsiT
LWExpTerm     Loop: KLK_rotate KLloopOf blockMat etaT_eq_zt_im etaT_pos loopFine loopM_eq_loopL
LWExpTerm4    Loop: KLK_rotate KLloopOf etaT_eq_zt_im etaT_pos norm_Lloop_le stKbound_of_flow stKward_of_flow
LWExpTerm6    Green: v3_premises_of_stFlow | Loop: etaT_pos
$ [B7b] python3 -I $SP/s_closure.py   # closures of chain files and imports of LW-14 files
Graph modules in the import closure of chain files that consume the L pins (the six pin-vocabulary modules; no graph proof):
  EMn2Exp2     6: Expansions LWPins LWPsi LWStein LWVocab ScalingOrder
  Step2Events  6: Expansions LWPins LWPsi LWStein LWVocab ScalingOrder
  Step6Kit     6: Expansions LWPins LWPsi LWStein LWVocab ScalingOrder
  EtermsMid    6: Expansions LWPins LWPsi LWStein LWVocab ScalingOrder
  ExpIntIQ     6: Expansions LWPins LWPsi LWStein LWVocab ScalingOrder
direct Induction/ imports of the LW-14 and aux files (the BA twins need their carrier forms or facts as hypotheses):
  LWExpTerm   ExpAvg ConArgDet
  LWExpTerm2  Step6Kit Step5Kit
  LWExpTerm3  ScaleFacts
  LWExpTerm4  Step34Pins ScaleFacts
  LWExpTerm6  ExpIntIQ ExpWardII ExpIntEasy
  AuxGraph2   ConArgDet PerTimeCalc DecayLoopB
$ [B8] python3 -I $SP/s_lane.py     # import graph; hub-log module times (25 logs build-T2356..T2385)
Graph modules upstream of (or among) the 6 certificate modules, 25 of 58 (an in-place edit rebuilds them):
  AuxGraph AuxGraph2 Expansions LWEdgeExp LWExpCert LWExpCertB LWExpCertBS0 LWExpCertBS1 LWExpCertS0 LWExpCertS1 LWExpTerm LWExpTerm2 LWExpTerm3 LWGGExp LWLvl1 LWPins LWPsi LWSizeClaim LWStein LWSymm LWVocab LWWeightExp LocalRegular LocalRegular2 ScalingOrder
not upstream: 33 modules (an in-place edit costs only its own cone), among them LWMoment LWMomentExp LWMomentExpA LWTermHolds LWTermExpN LWExpTerm4 LWExpTerm5 LWExpTerm6 LWExpSim LWExpSound LWProv LWEngine AnpKey*
in-place file  lines  cone cone-ln  cert non-cert min
LWMoment        1872     9    8682    no       4.4
LWMomentExp     1509     5    3961    no       3.4
LWMomentExpA     460     6    4421    no       3.7
LWTermHolds     1801     4    2452    no       1.4
LWTermExpN       546     8    5754    no       4.3
LWExpTerm4      1838     6    3466    no       0.9
LWExpTerm       1256    27   24268   YES       7.6
LWPins          1008   118  145148   YES      38.0
hub-log module times (s; 25 logs build-T2356..T2385): median [min, max], n
  LWExpCertBS0   1668.0 [ 1533.0,  4341.0] n=3
  LWExpCertBS1   2039.0 [ 1592.0,  2073.0] n=3
  LWExpCertS0     631.0 [  593.0,  1061.0] n=3
  LWExpCertS1     630.0 [  574.0,  1781.0] n=3
  LWExpCertB       12.0 [   10.0,    15.0] n=3
  LWExpCert         8.4 [    6.9,     9.7] n=3
non-certificate Graph modules with times: 22, 26469 lines, 528 s: 20.0 s per kloc
BS0+BS1 (the heavy pair): medians 61.8 min, minima 52.1 min; BA estimate 0.5-1.5 x: 31-93 min
```
```
$ [B9] python3 -I $SP/s_rows_b9c.py   # first three lines are the script header:
# Stage-L row table (T2387).  Basis = band lines of the segments listed in ROWS below (file, first line, last line, P ranges subtracted); the design report §6 prints them.
# Ratios (BA lines per band line): TW 0.73/0.85/1.61, NW 0.85/1.20/2.10 (T2378 §5 spread, graph centre 0.85 = BA-L2 2975/3490, T2325 table l.23);
# G rows: T2379 model (1-f) S g + f S 0.8 + 100 + 60 endpoints, g = 1.92 d_FLOW (T2379 B3 rho), f = 0.05/0.14/0.30, g x 0.75/1/1.5.
row   cl  basis    lo  centr    hi   (basis = band lines; * = certificate modules)
L0    F      0   190    250   350   |   L2c1  TW  1073   783    912  1728
L2c2  TW  1675  1223   1424  2697   |   L3a1  TW  1211   884   1029  1950
L3a2  TW  1115   814    948  1795   |   L3a3  TW  1611  1176   1369  2594
L3a4  TW  1569  1145   1334  2526   |   L3a5  TW  1186   866   1008  1909
L3b1  TW  1822  1330   1549  2933   |   L3b2  TW  1625  1186   1381  2616
L3b3  NW  1739  1478   2087  3652   |   L3b4  NW  1831  1556   2197  3845
L3b5  NW  1286  1093   1543  2701   |   L3b6  NW  1510  1284   1812  3171
L3c1  NW   841  1115   1409  2166   |   L3c2  NW  1108   942   1330  2327
L3c3  TW  2287  1670   1944  3682   |   L3d1  F      0   500    800  1200
L3d2  G   3841   799   1121  1646   |   L3d3  TW   937   684    796  1509
L3d4  TW  1820  1329   1547  2930   |   L5    G   2347   599    784  1088
L4a   G   1838   636    811  1086   |   L4a2  TW  1256   917   1068  2022
L4b   NW  2116  1799   2539  4444   |   L4c   NW  2301  1956   2761  4832
L4d   TW   677   494    575  1090   |   L4e1  NW   534   454    641  1121
L4e2* NW  1163   989   1396  2442   |   L4f1  TW  1211   884   1029  1950
L4f2  NW  1490  1266   1788  3129   |   L4g   NW   754   641    905  1583
L6    F      0   150    250   400
rows 33  by class (rows / band basis lines / central): TW 15 / 21075 / 17913; NW 12 / 16673 / 20408; G 3 / 8026 / 2716; F 3 / 0 / 1300
route T (twin everything, copy tax paid): lo 32832  central 42338  hi 75114
copy tax (ratio x band-free private lines inside the segments; upper bound of the publishing saving): 2641
planning ratio 1.144 (supervisor 0853): central 48434
rows with central > 1500 (may split at ticket time): ['L3b1', 'L3b3', 'L3b4', 'L3b5', 'L3b6', 'L3c3', 'L3d4', 'L4b', 'L4c', 'L4f2']
tickets at 1000 lines per ticket (T2325 s7): central 42.3  lo 32.8  hi 75.1 ; with 1.144: 48.4
critical path (import order): 15 rows, 20110 central lines: L2c2 L3a1 L3a3 L3a4 L3a5 L3b1 L3b2 L3b3 L3b4 L3b5 L3b6 L3d3 L3d4 L5 L6
rows without a predecessor (start at the opening): L0 L2c1 L2c2 L3c2 L4a L4a2
$ [B10] python3 -I $SP/gg_check.py | tail -6; python3 -I $SP/gg_check2.py | tail -4   # printed vs corrected (D402) GGGamma
lanlw  f=1 : |L-R|=1.62e-16   L=(-0.05161765+0.075738501j)
lanlw  f=Gc: |L-R|=1.42e-15   L=(0.232387433+0.141740167j)
GG (GGGamma) at x=y=y'=1, f=1:  LHS=(0.232387433+0.141740167j)
   as printed (S+ in groups 1-2):      RHS=(-0.477774332-0.17510402j)  |LHS-RHS|=7.776e-01
   with M+ S+ in groups 1-2 (derived): RHS=(0.232387433+0.141740167j)  |LHS-RHS|=2.289e-16
M=(-0.15+0.988686j)  M+=(-0.955-0.296606j)  S=0.5000  S+=(0.335034-0.033629j)
GG printed  max|LHS-RHS| over (x,y,y',a,b) in {0,1}^5: 8.572e-01
GG derived  max|LHS-RHS| over (x,y,y',a,b) in {0,1}^5: 3.335e-15
M offdiag |M_01| = 0.3489, |M_00| = 0.9372, |M+_01| = 0.1217
$ [B11] sed -n 'Np' paper/tex/B_graphical_lemmas.tex (N = 98 118 275 302 318 407 416 494 522), 7_8:88, 1_2:1107-1110, LocalRegular6a.lean:24, Kernel/PropT.lean:10 (cut at 118 chars)
B:98  The three remaining cases below all rest on the following fact, which is verified by inspecting the terms on the right
B:118 The proof of \Cref{lem:LWterm_EXP} for the block Anderson model is analogous to the argument above, except that the $G
B:275 It remains to expand such graphs $\cal G$ using the edge expansion \eqref{Oe1x} and the $GG$ expansion \eqref{Oe2x}. A
B:302 begin{definition}[Atoms and atomic graphs]\label{def_atom}
B:318 hbox{$x$, $y$ belong to the same atom} \implies x-W[x] = y-W[y],\ \text{and} \ |[x]-[y]|\le (\log W)^{1+\e_1}.
B:407 As explained in \cite[Appendix B]{yang2024Del}, repeated applications of the above local expansions to an arbitrary no
B:416 We begin by applying the local expansion to the graph $|f_{xy}(G)|^p$. This allows us to establish the same result as 
B:494 The only difference from the random band matrix case is that the ``summation over a molecule'' here also includes summ
B:522 For the proof of \Cref{lem:LW_moment_exp}, the bounds in \eqref{eq:Gbyxi2_BA} remain valid with $\Psi_t(|[\al]-[\beta]
7:88  For the proof of \Cref{lem: EWGn2_N}, as discussed below \eqref{eq:directG1}, it suffices to assume that $1-t>\ilambda
1_2:1107-1110 \begin{equation}\label{eq_B_param} B_{t, K}:=\frac{(\ilambda^{2}+|1-t|)^{-1}}{(K+1)^{d-2}}+\frac{1}{L^d|1-t|},\q
Graph/LocalRegular6a.lean:24 The paper tracks `ord + n_dv + n_lw` along `strat_local` and asserts a monotone step (`B:275-277`);
Kernel/PropT.lean:10 # `lem:propT`: the convolution bound `(TTT2)` for the tail function
$ [B12] python3 -I $SP/s_dens2.py $WT LWPins ... LWEngine; python3 -I $SP/s_pub.py | tail -1   # line-level mention densities; band-free private lines
file              lines   code  dFLOW dSHAPE     gF     gS
LWPins             1008    373  0.287  0.000   0.55   0.00
LWTermHolds        1801   1475  0.112  0.000   0.21   0.00
LWTermExpN          546    390  0.036  0.000   0.07   0.00
LWMoment           1872   1521  0.126  0.003   0.24   0.01
LWMomentExp        1509   1325  0.095  0.004   0.18   0.01
LWMomentExpA        460    315  0.041  0.000   0.08   0.00
LWExpTerm4         1838   1401  0.188  0.000   0.36   0.00
LWExpTerm          1256    951  0.204  0.000   0.39   0.00
LWExpTerm2         2116   1621  0.165  0.006   0.32   0.01
AuxGraph2          1500   1070  0.096  0.000   0.18   0.00
LWLvl1             4462   3228  0.000  0.445   0.00   0.85
LWSymm             2326   1523  0.001  0.486   0.00   0.93
LWEngine            937    530  0.000  0.374   0.00   0.72
band-free private lines: upstream of a certificate module (publishing edit joins the lane): 2190 ; elsewhere: 2831
```

Narrative (b):
- Branch state: probe commits `70e371c`, `97550e0`, then `5c3245e` (docstring: the first-sum order instance names the external `y, y'`) and `fe433f2` (docstring: the `STMainIndG` line at the base). `git diff --stat main...t/T2387` is the probe only (B0); the design report and this report are in the main worktree (the hub commits them at merge).
- Every number of the design report comes from B1-B12 (this session) or from cited file lines. The census B6 reads statement tokens; the row table B9 applies ratios measured on merged BA files (BA-L2: 0.85) and the T2378 §5 spread to explicit band-line segments, and prices the three G rows with the T2379 model and the line-level density of B12. Limits: design §8.
- No hypothesis was added, no pinned signature changed, no file outside the two writable files written.

## (c) Verified Mathlib and Lean names
- Mathlib, each used in the compiled probe (B1): `Real.rpow_le_rpow_of_exponent_le` (probe 319, 359-360), `Eventually.of_forall` (359, 378, 382), `Ring.mul_inverse_cancel` (278, 290), `Real.log_nonneg` (362), `Nat.ceil_natCast` (303), `Matrix.one_apply_ne` (281), `Matrix.mul_apply` (280), `Finset.sum_eq_single` (280), `Finset.card_pos` (273), `Finset.mem_filter` (274).
- Verified absent on `main` 76458c2 (checked 16:21 UTC): `RBM3D/Chain/Step2Gen.lean` (`ls RBM3D/Chain`: `Carrier.lean` only), `STKwardgL` (no hit outside `Probe/`; `STKboundgL` is `Chain/Carrier.lean:146`), `BAMfine_block_zero` (`git grep` finds it on `t/T2378` only, `Probe/T2378Pins.lean:126`).

## (d) Open issues and paper-delta candidates
Open issues: (1) T2386 (`Chain/Step2Gen`) is not merged: the probe forms `STLWBG`, `STLWTG`, `STEMn2ExpG` follow T2386 target 2(b)/(c) and the `STStep2G` shape (`t/T2379` probe 39-104); names may become `…gL`; (2) the probe is at 399 of 400 lines: the S-route precondition and the BA certificate model are not compiled; (3) census, densities and ratios are readings and models (design §8); (4) the stage-G pins (supervisor C3) are not merged: rows L3c3, L3d2, L5 take them as hypotheses.
Paper-delta candidates (temporary tags; the dispatcher numbers them):
- `T2387a` (evidence for `T2161a`): `GGGamma` (`B:393-405`) prints `S⁺_{xβ}` in its first two sums; the identity needs `(W-1)_{xβ} = (M⁺S⁺)_{xβ}`. Printed form fails (B10: 7.8e-1 at `N = 1`, 8.6e-1 over `{0,1}^5` at `N = 2`), corrected form holds (2.3e-16, 3.3e-15); compiled `ba_W_sub_one` (probe 287), pin `BAGGGamma` (probe 344).
- `T2387b`: `(eq:GGraisesord)` (`B:98-100`) is stated for the terms of the expansion without context; at BA the first sum at external `y, y'` keeps the order of its parent (compiled `baGGT1_ord`, `baGGLhs_ord`, probe 313).
- `T2387c`: `B:416` ("properties (1)-(6) ... continue to hold") for BA: the band step for (6) fails (`LocalRegular6a.lean:24`, DECISIONS §47) and the BA statement has no argument.
- `T2387d`: `B:407` cites [yang2024Del] App. B (arXiv:2501.08608, `Jun.bib:254-259`) for the BA lvl1 analogue; the text is not in the repository and DECISIONS §5 authorises only LSY Thm 2.2.
- `T2387e`: the scalar-`M` hypothesis of `LWGtoAG`, `lwClaimSize` fails at every BA datum with `g₀ ≠ 0`, `Im m > 0` (compiled, probe 253; `T2325b` is the instance-level statement).
- `T2387f`: `(G_by_auxG_BA)` (`B:489`): the exponent `ord G - ord G^aux ≥ n_S^{within} ≥ 0` is not in the paper ((a′) row 15).
