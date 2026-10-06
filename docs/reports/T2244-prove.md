Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 02:40:57 UTC 2026

Scope: `un_gueLocal_of_tail : UNGUESchurTail → UNGUELocal` and its deterministic bootstrap (RBM2D `Universality/GUELocalBootstrap.lean`, read at `:341-1042`; the check file compiles, CONTROL `done:` 02:33:21 UTC exit 0). Notation: `N = Nsz sz n = (W L)^d`, `s = N^{-τ/4}`, `c = cGap κ = √(κ(4-κ))`, `h = glMesh N = N^{-4}`.

### (i) Exponent table

| quantity | value | constraint / where it is used | slack |
|---|---|---|---|
| `κ' = min κ 2` | `κ=1`: 1 | `0<κ'≤2` (`cGap_pos`, `glE_le`); `|Re z|≤2-κ ⇒ ≤2-κ'` | none needed |
| `τ' = min τ (1/2)` | `τ=1/10`: 1/10 | `0<τ'`, `τ'≤1/2` (`gue_local_det`), `τ'≤1` (`glPts_mem`, `glPts_card`, `card_glPts_le`); `N^{τ'}≤N^τ`, `N^{-1+τ}≤N^{-1+τ'}` for `N≥1` | `1/2 - τ' = 0.4` |
| `ε = τ'/4`, `q = 9`, `D` | `1/40`, 9, `D=2` | `0<ε`, `0<D` (tail pin); grid card `≤ N^q` | see grid row |
| `c = cGap κ` | `cGap 1 = 1.7321`, `cGap 2 = 2`, `cGap(1/100)=0.1997` | `c ≤ ‖2m_sc+z‖` since `(2m_sc+z)² = z²-4` (`msc_disc_sq`) and `|z²-4| ≥ 4+y²-x² ≥ κ(4-κ)` for `|x|≤2-κ`; `c ≤ 2` | `c>0` iff `0<κ≤2` |
| stability | `|m-m_sc| ≤ 2Λ/c` | `m(z+m)+1 = δ(δ+2m_sc+z)`, `δ=m-m_sc`; needs `|δ|≤c/2` (so `|δ|(c-c/2) ≤ Λ`) | exact |
| residual / `|G_ii|≤2` | `Λ = 2υ`, so one step gives `4υ/c` | `|G_ii^{-1}| = |-(z+m)+Υ_i| ≥ ‖m_sc+z‖ - |δ| - |Υ_i| > 1 - 1/4 - 1/4 = 1/2` (`norm_msc_add_z_gt_one`) | `|G_ii|≤2` exact |
| chain start `η_0 = 10` | `‖m‖,‖m_sc‖ ≤ 1/10` (`1/η`) | `|δ_0| ≤ 1/5 ≤ min(10/2, 1/4)`, `c_0 = 10 ≤ ‖2m_sc+z‖` (`im_le_norm_two_msc_add_z`); `Im m ≤ 1/10 ≤ 2` | `1/4 - 1/5 = 0.05` |
| mesh `h` | `N^{-4}` | step: `2h/(η_kη_{k+1}) ≤ 2s` for `η ≥ N^{-1+τ} ≥ N^{-1}` (`jump_le`, `τ≤8`) | at `N=2^21`: `2.5e-14 ≤ 1.39` |
| `GlSmall` N55 | `N ≥ 55` | `card_glPts_le` | — |
| `GlSmall` h1 | `6s ≤ 1/4` | `υ_k ≤ 1/4` (`budSimp_le`: `budSimp ≤ 6s` since `Nη ≥ N^τ`) | `N=1e80`: 0.06 vs 0.25 |
| `GlSmall` h2 | `24s/c + 2s ≤ min(c/2,1/4)` | chain step `4υ_k/c + 2h/(ηη') ≤ min(c/2,1/4)` with `υ_k ≤ 6s` | binding: `κ=1`, `1/4` side; `15.856 s ≤ 0.25` |
| `GlSmall` h3 | `24 N^{τ/4}/c + 13 ≤ N^τ` | final: `4υ/c + (2+2)h/η² ≤ (24N^{τ/4}/c + 13)/√(Nη) ≤ N^τ/√(Nη)` | `N=1e80`: 1398.6 vs 1e8 |
| first `N` with `GlSmall N 1 (1/10)` | `log10 N = 72.0906` (`N ≈ 1.23e72`) | h2 binds; h1, h3, N55 hold from there; no failure at 250 sampled `log10 N ∈ [72.09, 197]` | RBM2D docstring says "≈ 10^73": ours is `10^72.09` |
| grid | `J ≤ 4N^4`, `K ≤ 10N^4`; `(J+1)(K+1) ≤ 40N^8+14N^4+1 ≤ 55N^8 ≤ N^9` | `card ≤ N^9` for `N≥55` | at `N=55`: `3.35e15 ≤ 4.61e15` (factor 1.375) |
| lift `interp_le` | `4h/η² ≤ 13/√(Nη)` on `N^{-1+τ} ≤ η ≤ 10` | `η ≥ N^{-1}` gives lhs `≤ 4N^{-2}`; `√(Nη) ≤ √(10N)`; two Lipschitz terms of `≤ 2h/(η η_g) ≤ 2h/η²` each (`|z-z_g| ≤ 2h`, `η_g ≥ η`) | `N=55,η=10`: `4.4e-9 ≤ 0.55` |
| lift (§64 (4)) | bound `N^τ/√(Nη)` deterministic | `Im m_N ≤ 2` and Schur error used only at grid points (hypothesis `hΓ`); never lifted | n/a |
| `d` | enters only through `Idx d`, `Ω d`, `gueP d`, `Xmat d` | `N = (WL)^d ≥ 1` from `three_le_L`, `W_pos` (also `card_Idx`): `Nonempty (Idx d L W)` by `Fintype.card_pos`; `Sizes d` has no `3≤d` field (`sz0 : Sizes 3`) | no exponent involves `d` |
| `sz0` (`d=3`) | `N_n = ((2(n+1))^5 · 4(n+1))^3 = 2097152 (n+1)^18` | `N_n → ∞`; `N_0 = 2097152` (= `card_Idx_sz0`) | first `n` with `GlSmall`: 4506 |

Consumer token check (conclusion of `un_gueLocal_of_tail` against `UNGUELocal`, `Pins.lean:489-495`): same binders `d, 3≤d, sz, size→∞, κ τ D, 0<κ,0<τ,0<D`; same event `{ω | ∃ z, |z.re|≤2-κ ∧ N^(-1+τ)≤z.im ∧ z.im≤10 ∧ N^τ/√(N z.im) < ‖stieltjesN (Xmat …) z - msc z‖}`; same bound `ofReal (N^(-D))`. Reduction: the event for `(κ,τ)` is inside the tail failure event at `(κ',τ',ε,D,q=9,Γ_n = glPts N κ' τ')`; off that failure event the hypothesis `hΓ` of `gue_local_det` holds, which gives `‖m_N-m_sc‖ ≤ N^{τ'}/√(Nη) ≤ N^τ/√(Nη)`, contradicting the event. `Γ_n` lies in the window (`glPts_mem`) with `card ≤ N^9` eventually (`glPts_card`); `GlSmall` holds eventually (`glSmall_eventually`, `N_n→∞`). `UNGUESchurTail` (check 2.1) has the carrier of RBM2D `GUESchurTail` `:908` with `Sizes d + 3≤d` and `Nsz sz n`.

`Gres` bridge: `stieltjesN M z = (card)⁻¹ * (Gres M z true).trace` (`Pins.lean:88-89`); `Gres H z true = Ring.inverse (H - z•1)` and `green H z = (H - z•1)⁻¹`, equal by `Matrix.nonsing_inv_eq_ringInverse` (template `InjSum.lean:76`, `simp only [green, Gres, ↓reduceIte, …]`). `norm_Gsig_le_inv_eta hH hη (hz : η ≤ |z.im|) true : ‖Gres H z true‖ ≤ η⁻¹` (`FlowCalculus.lean:644-649`) with `η = z.im`, `hz : z.im ≤ |z.im|` replaces RBM2D `norm_green_le`. `sc_residual` uses only `trace = Σ G_ii` and `G_ii ≠ 0`; the identity `m(z+m)+1 = N⁻¹ Σ_i Υ_i G_ii` follows from `Υ_i G_ii = 1 + (z+m) G_ii` (`G_ii^{-1} = Υ_i - z - m`) and `N⁻¹ Σ G_ii = m`.

### (ii) One concrete nondegenerate instance

Instance: `d = 3`, `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`), `κ = 1`, `τ = 1/10`, `κ' = 1`, `τ' = 1/10`, `ε = 1/40`, `D = 2`, `q = 9`. Window `|Re z| ≤ 1`, `N^{-9/10} ≤ Im z ≤ 10`. Hypotheses: `3 ≤ 3`; `size → ∞` (`N_n = 2097152 (n+1)^18`); `0<1`; `1 ≤ 2`; `0<1/10 ≤ 1/2`; grid in window and `card ≤ N^9` (eventually, `N ≥ 55`); `GlSmall` eventually, and at `N = 10^80`. `UNGUESchurTail` stays a hypothesis (UN-10, owed); the limit computation below is for the deterministic part.

Command: `python3 .../scratchpad/T2244/pre.py` (mpmath, 60 digits). Output (verbatim):

```
cGap(1)= 1.73205080756887729352744634150587236694280525381038062805581  cGap(2)= 2.0  cGap(1/100)= 0.199749843554381789157803823280582871978625761166414365377831
N=1e70 (True, True, False, True) ['0.106697', '0.281971', '0.25', '792.203', '1.0e+7']
N=1e72 (True, True, False, True) ['0.0950936', '0.251307', '0.25', '887.28', '1.58489e+7']
N=1e73 (True, True, True, True) ['0.0897741', '0.237249', '0.25', '939.084', '1.99526e+7']
N=1e74 (True, True, True, True) ['0.0847523', '0.223978', '0.25', '993.958', '2.51189e+7']
N=1e80 (True, True, True, True) ['0.06', '0.158564', '0.25', '1398.64', '1.0e+8']
first N with GlSmall (bisection): log10 N = 72.09059
72.08059 (True, True, False, True)
72.09059 (True, True, True, True)
failures above threshold (sampled): []
N_0 = 2097152  (2^21 = 2097152 )  formula 2097152*(n+1)^18 ok: True
first n of sz0 with N_n >= threshold: 4506  N_n=1.23483e+72 GlSmall there: (True, True, True, True)
GlSmall at n=lo_n-1: (True, True, False, True)
N=55.0 (J+1)(K+1)=1.67013e+15 <= (4N^4+1)(10N^4+1)=3.34936e+15 <= N^9=4.60537e+15 : True
N=56.0 (J+1)(K+1)=1.92918e+15 <= (4N^4+1)(10N^4+1)=3.86869e+15 <= N^9=5.41617e+15 : True
N=100.0 (J+1)(K+1)=1.99683e+17 <= (4N^4+1)(10N^4+1)=4.0e+17 <= N^9=1.0e+18 : True
N=2097152.0 (J+1)(K+1)=7.48289e+51 <= (4N^4+1)(10N^4+1)=1.49658e+52 <= N^9=7.84638e+56 : True
55^9/(55^8*40+14*55^4+1)= 1.375
grid pt j=0,k=0: E=-1 (|E|<=1), eta=10; window N^(-0.9)= 2.04425e-6 <=10 : True
jump worst: 5.02377e-161 <= 2N^-tau/4 = 0.0299247
jump worst: 2.47425e-14 <= 2N^-tau/4 = 1.38992
interp N=1e1.74 eta=0.02714: lhs=0.000593283 rhs=10.6396
interp N=1e1.74 eta=10.0: lhs=4.37129e-9 rhs=0.554322
interp N=1e73.0 eta=1.995e-66: lhs=1.00475e-160 rhs=0.00291034
interp N=1e73.0 eta=10.0: lhs=4.0e-294 rhs=1.3e-36
tau'/4 = 0.025 kappa' = min(1,2) = 1
start: 1/10+1/10 = 0.2  <= min(5,1/4)= 0.25
```

Reading the `N=1e..` rows: the tuple is `(N55, h1, h2, h3)`; the list is `[6s, 24s/c+2s, min(c/2,1/4), 24N^{τ/4}/c+13, N^τ]`. Nondegeneracy: `N_0 = 2097152 ≥ 55`, grid at `n=0` has `J = ⌊2/N^{-4}⌋`, `K = ⌊(10 - N^{-0.9})/N^{-4}⌋`, so it contains `-1 + 10i` (nonempty), window not collapsed (`-1 ≤ Re ≤ 1`, `2.0e-6 ≤ Im ≤ 10`). `GlSmall` is eventual (`n ≥ 4506` for `sz0`) and holds at `N = 10^80` (all four conditions True, row `N=1e80`). The instance `inst_glSmall_witness` is the `N=1e80` row.

External hypothesis `UNGUESchurTail` (TEAM §8 lesson 14: concrete limit computation). Deterministic content: along `sz0`, `N_n → ∞`, `s = N_n^{-1/40} → 0`, and h1, h2, h3 hold from `n = 4506` on (output above); the failure budget `N^{-D}` with `D = 2` and union over `≤ N^9 · N` pairs `(z,i)` requires per-pair failure `≤ N^{-12}`, which the Gaussian/Hanson-Wright tails give with `ε`-loss `N^{ε}` because `√(log)` growth is `≪ N^{1/40}` (route RBM2D `:899-907`: Schur complement, `|h_ii| ≺ N^{-1/2}`, quadratic chaos, Ward identity, union bound). Numerical sanity (GUE `H = (X+X*)/√2`, `X_ij ~ CN(0,1/N)`, `κ=1`, `τ=1/10`, 50 grid points `Re ∈ linspace(-1,1,10)`, `Im ∈ geomspace(N^{-0.9},10,5)`), commands `python3 num.py` and `python3 num2.py` in the same directory:

```
N=2000 samples=20 gridpts=50
max_{z,i,omega} |Upsilon_i| / schurBud(N,1/40,z) = 3.2615 (<=1 expected)
max_{z,omega} |m_N-m_sc| sqrt(N eta)/N^(1/10)   = 0.3917 (<=1 expected)
max Im m_N = 1.4048 (<=2)
N= 250  N^eps=1.148  max|Ups|/bud0=3.614  median over (z,omega) of max_i=1.519  max/N^eps=3.148
N= 500  N^eps=1.168  max|Ups|/bud0=3.629  median over (z,omega) of max_i=1.581  max/N^eps=3.107
N=1000  N^eps=1.189  max|Ups|/bud0=3.600  median over (z,omega) of max_i=1.703  max/N^eps=3.029
N=2000  N^eps=1.209  max|Ups|/bud0=3.746  median over (z,omega) of max_i=1.821  max/N^eps=3.098
```

(`bud0 = N^{-1/2} + (2/(Nη))^{1/2} + (Nη)^{-1}` is `schurBud` without the factor `N^ε`.) The expected ratio `≤ 1` is false at these sizes: the sup of `|Υ_i|/bud0` over `2000` rows, 50 points and 20 samples is about `3.6` (flat in `N`, as a Gaussian-maximum constant), while `N^{1/40} = 1.2`. This is a finite-size constant, not a counterexample: the pin is `∀ᶠ n` at fixed `ε = 1/40`, and `N^{1/40} ≥ 3.75` first for `N ≥ 3.75^40 ≈ 10^{22.96}`, below the `GlSmall` threshold `10^{72.09}`. The second ratio (law itself) is `0.39 ≤ 1` at `N=2000`. The instances therefore keep `UNGUESchurTail` as a hypothesis (as the ticket says) and nothing in this section claims it is tested at small `N`.

### Verdicts

- Target 1 (`msc` facts, check 2.2): PASS. All statements are identities or inequalities on `ℂ` (`(2m_sc+z)² = z²-4`, `Im`-lower bounds, stability) verified in (i).
- Target 2 (self-consistent equation, check 2.3): PASS. The `Gres`/`green` bridge reduces `stieltjesN` to the RBM2D form; `‖G‖ ≤ 1/η` from `norm_Gsig_le_inv_eta`; `Nonempty ι` is a hypothesis as in the check.
- Target 3 (chain, budget, grid, `gue_local_det`, `glSmall_eventually`, check 2.4): PASS. Constants close (rows h1, h2, h3, grid, `interp_le`, `jump_le`); `N ≥ 55` is the only size threshold in the deterministic part.
- Target 4 (`glPts_mem`, `glPts_card`, `un_gueLocal_of_tail`, check 2.5): PASS. Token check above; `UNGUESchurTail` is the premise; no `d`-dependent exponent.
- Target 5 (instances, check 2.6): PASS. `inst_glSmall_witness` at `N = 10^80` (all four `GlSmall` conditions True); `inst_grid_nonempty` at `N = 2097152`; `inst_schurTail`, `inst_gueLocal` at `sz0` with `UNGUESchurTail` kept as hypothesis.

Overall verdict: PASS.

## (b) Script output (stage 1b, prover-hard, claude-sonnet-5-5; written Tue Oct  6 02:54:52 UTC 2026)

Scratch scripts and their outputs are in `T2244/` of the session scratchpad; the commands below are verbatim.

```
$ date -u; git rev-parse --short HEAD; git diff --stat main...t/T2244
Tue Oct  6 02:51:49 UTC 2026
06eefc8
 RBM3D/Test/Axioms.lean                    |    1 +
 RBM3D/Universality/GUELocalBootstrap.lean | 1146 +++++++++++++++++++++++++++++
 2 files changed, 1147 insertions(+)

$ lake build RBM3D.Universality.GUELocalBootstrap 2>&1 | tail -2
Note: This linter can be disabled with `set_option linter.unusedDecidableInType false`
Build completed successfully (3367 jobs).
$ lake env lean RBM3D/Universality/GUELocalBootstrap.lean  (fresh elaboration; diagnostics in the file)
exit 0; output lines:        0

$ lake build   (full library, in the worktree; root #assert_rbm_axioms and Test/AuditNegative; run 02:49:13-02:49:55 UTC)
Build completed successfully (4047 jobs).
exit 0
error lines: 0

$ lake env lean precheck.lean   (import RBM3D; import RBM3D.Universality.GUELocalBootstrap; #assert_rbm_axioms)
Tue Oct  6 02:51:57 UTC 2026
exit 0
axiom audit: 7110 theorems, 2398 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
164:premises found by scanning: 145 (borrowed 1, owed 106, structural 32, refuted 6).
165:registry: 2 borrowed + 155 owed + 91 structural + 7 refuted; 110 registered premise(s) carry nothing yet: [RBM.Loop.
  RBM.Univ.UNGUELocal: 41 [no certificate]
  RBM.Univ.UNGUESchurTail: 3 [no certificate]
main's registry (git show HEAD~1:RBM3D/Test/Axioms.lean, parsed): owed 154 -> branch owed 155

$ for each of the 50 new public declarations: #print axioms (aggregated: sed -E "s/^.[^.]*. //" | sort | uniq -c)
  50 depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.un_gueLocal_of_tail' axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.gue_local_det' axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUELocalBootstrapInst.inst_schurTail' axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUELocalBootstrapInst.inst_gueLocal' axioms: [propext, Classical.choice, Quot.sound]
```

```
$ python3 extract.py <targets 1-4>   (statements extracted from RBM3D/Universality/GUELocalBootstrap.lean, whitespace-joined)
norm_msc_add_z_gt_one {z : ℂ} (hz : 0 < z.im) : 1 < ‖msc z + z‖
im_le_norm_msc_add_z {z : ℂ} (hz : 0 < z.im) : z.im ≤ ‖msc z + z‖
norm_msc_le_inv_im {z : ℂ} (hz : 0 < z.im) : ‖msc z‖ ≤ (z.im)⁻¹
msc_disc_sq (z : ℂ) : (2 * msc z + z) ^ 2 = z ^ 2 - 4
sqrt_le_norm_two_msc_add_z {z : ℂ} {κ : ℝ} (hκ : 0 < κ) (hx : |z.re| ≤ 2 - κ) : Real.sqrt (κ * (4 - κ)) ≤ ‖2 * msc z + z‖
im_le_norm_two_msc_add_z {z : ℂ} (hz : 0 < z.im) : z.im ≤ ‖2 * msc z + z‖
sc_stability {m z : ℂ} {c Λ : ℝ} (hc : 0 < c) (hcz : c ≤ ‖2 * msc z + z‖) (hres : ‖m * (z + m) + 1‖ ≤ Λ) (hnear : ‖m - msc z‖ ≤ c / 2) : ‖m - msc z‖ ≤ 2 * Λ / c
norm_msc_sub_le {z z' : ℂ} (hz : 0 < z.im) (hz' : 0 < z'.im) : ‖msc z - msc z'‖ ≤ ‖z - z'‖ / (z.im * z'.im)
sc_residual [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) : stieltjesN H z * (z + stieltjesN H z) + 1 = (Fintype.card ι : ℂ)⁻¹ * ∑ i, schurErr H z i * green H z i i
norm_green_diag_le_two {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) (i : ι) (hΥ : ‖schurErr H z i‖ ≤ 1 / 4) (hm : ‖stieltjesN H z - msc z‖ ≤ 1 / 4) : ‖green H z i i‖ ≤ 2
sc_one_step [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) {c υ : ℝ} (hc : 0 < c) (hcz : c ≤ ‖2 * msc z + z‖) (hυ : υ ≤ 1 / 4) (hΥ : ∀ i, ‖schurErr H z i‖ ≤ υ) (hnear : ‖stieltjesN H z - msc z‖ ≤ min (c / 2) (1 / 4)) : ‖stieltjesN H z - msc z‖ ≤ 4 * υ / c
norm_stieltjesN_le [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) : ‖stieltjesN H z‖ ≤ (z.im)⁻¹
norm_stieltjesN_sub_le [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z z' : ℂ} (hz : 0 < z.im) (hz' : 0 < z'.im) : ‖stieltjesN H z - stieltjesN H z'‖ ≤ ‖z - z'‖ / (z.im * z'.im)
chain_bound [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) {x : ℝ} (hx : |x| ≤ 2 - κ) {h : ℝ} (hh : 0 < h) {K : ℕ} {η : ℕ → ℝ} (hη : ∀ k, η k = 10 - k * h) (hηpos : ∀ k ≤ K, 0 < η k) {υ : ℕ → ℝ} (hυ : ∀ k ≤ K, υ k ≤ 1 / 4) (hΥ : ∀ k ≤ K, ∀ i, (stieltjesN H ⟨x, η k⟩).im ≤ 2 → ‖schurErr H ⟨x, η k⟩ i‖ ≤ υ k) (hstep : ∀ k, k + 1 ≤ K → 4 * υ k / cGap κ + 2 * h / (η k * η (k + 1)) ≤ min (cGap κ / 2) (1 / 4)) : ∀ k ≤ K, ‖stieltjesN H ⟨x, η k⟩ - msc ⟨x, η k⟩‖ ≤ 4 * υ k / cGap κ
schurBud_le {N ε : ℝ} (hN : 1 ≤ N) {z : ℂ} (hη1 : 1 ≤ N * z.im) (hη10 : z.im ≤ 10) : schurBud N ε z ≤ budSimp N ε z.im
exists_glPt {N κ τ : ℝ} (hN : 0 < N) {z : ℂ} (hx : |z.re| ≤ 2 - κ) (hη1 : N ^ (-1 + τ) ≤ z.im) (hη2 : z.im ≤ 10) : ∃ j k : ℕ, j ≤ glJ N κ ∧ k ≤ glK N τ ∧ 0 ≤ z.re - glE N κ j ∧ z.re - glE N κ j ≤ glMesh N ∧ 0 ≤ glEta N k - z.im ∧ glEta N k - z.im ≤ glMesh N
interp_le {N τ η : ℝ} (hN : 1 ≤ N) (hτ : 0 < τ) (hη : N ^ (-1 + τ) ≤ η) (hη10 : η ≤ 10) : 4 * glMesh N / (η * η) ≤ 13 / Real.sqrt (N * η)
card_glPts_le {N κ τ : ℝ} (hN : 55 ≤ N) (hκ : 0 < κ) (hκ2 : κ ≤ 2) (hτ : τ ≤ 1) : ((glPts N κ τ).card : ℝ) ≤ N ^ 9
gue_local_det [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {κ τ N : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) (hτ : 0 < τ) (hτ2 : τ ≤ 1 / 2) (hs : GlSmall N κ τ) (hΓ : ∀ z ∈ glPts N κ τ, ∀ i, (stieltjesN H z).im ≤ 2 → ‖schurErr H z i‖ ≤ schurBud N (τ / 4) z) : ∀ z : ℂ, |z.re| ≤ 2 - κ → N ^ (-1 + τ) ≤ z.im → z.im ≤ 10 → ‖stieltjesN H z - msc z‖ ≤ N ^ τ / Real.sqrt (N * z.im)
glSmall_eventually {κ τ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) (hτ : 0 < τ) {N : ℕ → ℝ} (hN : Tendsto N atTop atTop) : ∀ᶠ n in atTop, GlSmall (N n) κ τ
glPts_mem {d : ℕ} (sz : Sizes d) {κ τ : ℝ} (hκ2 : κ ≤ 2) (hτ1 : τ ≤ 1) (n : ℕ) : ∀ z ∈ glPts (Nsz sz n) κ τ, |z.re| ≤ 2 - κ ∧ Nsz sz n ^ (-1 + τ) ≤ z.im ∧ z.im ≤ 10
glPts_card {d : ℕ} (sz : Sizes d) (hd : Tendsto (fun n => sz.size n) atTop atTop) {κ τ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) (hτ1 : τ ≤ 1) : ∀ᶠ n in atTop, (((glPts (Nsz sz n) κ τ).card : ℕ) : ℝ) ≤ Nsz sz n ^ 9
un_gueLocal_of_tail (h : UNGUESchurTail) : UNGUELocal

$ python3 vocabdiff.py   (check section 2.1 definitions vs the file, whitespace-normalised, `noncomputable` dropped)
schurErr DIFFERS
  check: def schurErr {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (z : ℂ) (i : ι) : ℂ := (green H z i i)⁻¹ + z + stieltjesN H z
  lib  : def schurErr (H : Matrix ι ι ℂ) (z : ℂ) (i : ι) : ℂ := (green H z i i)⁻¹ + z + stieltjesN H z
cGap IDENTICAL
identical definitions: 11

$ lake env lean check_lib.lean / check_local.lean   (check file; 28 `example : T2244_x := @RBM.Univ.x` after the section 2.1 vocabulary removed / kept)
check_lib: exit 0; error lines 0; examples 28
check_local: exit 0; error lines 0; examples 28

$ python3 extract.py <instances>   (target 5; the 14 `example` applications of targets 1-3 follow them in the file)
inst_schurTail (h : UNGUESchurTail) : ∀ᶠ n in atTop, gueP 3 (sz0.L n) (sz0.W n) {ω | ∃ z ∈ glPts (Nsz sz0 n) 1 (1 / 10), ∃ i : Idx 3 (sz0.L n) (sz0.W n), (stieltjesN (Xmat 3 (sz0.L n) (sz0.W n) ω) z).im ≤ 2 ∧ schurBud (Nsz sz0 n) (1 / 40) z < ‖schurErr (Xmat 3 (sz0.L n) (sz0.W n) ω) z i‖} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ)))
inst_Nsz_zero : Nsz sz0 0 = 2097152
inst_grid_nonempty : (glPts (2097152 : ℝ) 1 (1 / 10)).Nonempty
inst_grid_nonempty_sz0 : (glPts (Nsz sz0 0) 1 (1 / 10)).Nonempty
inst_glSmall : ∀ᶠ n in atTop, GlSmall (Nsz sz0 n) 1 (1 / 10)
inst_gueLocal (h : UNGUESchurTail) : ∀ᶠ n in atTop, gueP 3 (sz0.L n) (sz0.W n) {ω | ∃ z : ℂ, |z.re| ≤ 2 - 1 ∧ Nsz sz0 n ^ (-1 + 1 / 10 : ℝ) ≤ z.im ∧ z.im ≤ 10 ∧ Nsz sz0 n ^ (1 / 10 : ℝ) / Real.sqrt (Nsz sz0 n * z.im) < ‖stieltjesN (Xmat 3 (sz0.L n) (sz0.W n) ω) z - msc z‖} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ)))
inst_glSmall_witness : GlSmall ((10 : ℝ) ^ (80 : ℕ)) 1 (1 / 10)
examples in the file: 14

$ clash.sh   (grep -rnw of the 50 new public short names in RBM3D/ and RBM3D.lean, new file excluded)
HIT un_gueLocal_of_tail 1
HIT UNGUESchurTail 1
distinct short names checked:       50; total hits outside the new file: 2
string GUELocalBootstrap outside the new file:
RBM3D/Universality/Pins.lean:488:Registry class: **owed** (UN: RBM2D `GUELocalSchur`, `GUELocalBootstrap`). Consumer (RBM2D `c9a24cf`): `Universality/GUETransla
(the 2 hits are the one registry line RBM3D/Test/Axioms.lean:230 of this branch)

$ python3 regcount.py
owedProps entries: base (HEAD~1) 154, branch 155

$ ports: git -C ../RBM2D --no-optional-locks log -1 --format=%h; diff --stat c9a24cf HEAD -- RBM2D/Universality/GUELocalBootstrap.lean; portdiff.py
9e0f275
 RBM2D/Universality/GUELocalBootstrap.lean | 87 ++++++-------------------------
 1 file changed, 16 insertions(+), 71 deletions(-)
RBM2D c9a24cf :73-882 (810 lines) vs RBM3D ported body (814 lines): 16 hunks, 23 removed, 27 added; rest verbatim
```

Narrative (every number above is script output).
- Files: new `RBM3D/Universality/GUELocalBootstrap.lean` (1146 lines at `06eefc8`, 1252 lines after the repair commit `23d9275`) and one line at `RBM3D/Test/Axioms.lean:230`, commits `06eefc8`, `23d9275` on `t/T2244`; `git diff --stat main...t/T2244` lists exactly these two files. No merged file is changed (`Pins.lean` and its `UNGUELocal` docstring untouched).
- Port of RBM2D `GUELocalBootstrap.lean` at `c9a24cf`: lines `:73-882` differ in 16 hunks (`portdiff.py`), the rest is verbatim. Changes: private bridge `GUELocalBootstrap_Gres_true` (template `InjSum.lean:76`), `GUELocalBootstrap_stieltjesN_eq` (`unfold stieltjesN` becomes `simp only [..._stieltjesN_eq]` at 3 places), `GUELocalBootstrap_norm_green_le` (from `RBM.Gauss.norm_Gsig_le_inv_eta ... true`; RBM2D `norm_green_le` has no RBM3D twin), `RBM.Gauss.isUnit_sub_smul_one_of_im_ne_zero` becomes `RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero`, private `msc_norm_mul` becomes `GUELocalBootstrap_msc_norm_mul`, two `show` become `change`.
- `GlSmall` is a `def` on `Prop`, the conjunction `N55 ∧ h1 ∧ h2 ∧ h3` of check 2.1 (the RBM2D `structure` has the same four fields in the same order); the proofs use `hs.1`, `hs.2.1`, `hs.2.2.1`, `hs.2.2.2`.
- `schurErr` is the check's text with the binders `{ι : Type*} [Fintype ι] [DecidableEq ι]` supplied by `variable` (file line 182); the other 11 definitions of check 2.1 are textually identical. The extracted statements above likewise omit these `variable` binders. The 28 scratch examples elaborate the check statements (instances at `Type`) against the library theorems, with the check vocabulary removed (`check_lib`) and kept (`check_local`).
- Assembly, new text: `UNGUESchurTail` (check 2.1 verbatim), `glPts_mem`/`glPts_card` at `{d} (sz : Sizes d)`, `un_gueLocal_of_tail` (proof of RBM2D `GUELocal_of_tail` `:944-982`); `Nonempty (Idx d (sz.L n) (sz.W n))` is a local `have` from `Sizes.card_Idx` and `1 ≤ Nsz sz n`, not a hypothesis of any pinned statement. `d` enters only through `Idx d`, `Ω d`, `gueP d`, `Xmat d` and `Nsz`; no exponent involves `d`.
- Instances (target 5): `inst_schurTail`, `inst_grid_nonempty`, `inst_glSmall`, `inst_gueLocal`, `inst_glSmall_witness` as in check 2.6, plus `inst_Nsz_zero` (`Nsz sz0 0 = 2097152`) and `inst_grid_nonempty_sz0`. `UNGUESchurTail` is the one kept hypothesis; `inst_glSmall_witness` is `GlSmall (10^80) 1 (1/10)` proved by `Real.rpow_natCast`, `Real.rpow_mul` and `norm_num` with `cGap 1 ≥ 1.7`.
- 19 `example`s (after the repair, `23d9275`) apply the other targets at concrete data: the six msc facts, `sc_stability` (`z = i`, `m = m_sc(i) + 1/2`, `c = 1`), `norm_msc_sub_le`, `norm_stieltjesN_le`, `norm_stieltjesN_sub_le`, `sc_residual`, `norm_green_diag_le_two` and `sc_one_step` (`H = 0` on `Unit`, `z = 10i`, `|Υ| = 1/10`), `chain_bound` (`H = 0` on `Unit`, `x = 0`, `κ = 2`, `h = 1`, `K = 1`, `η k = 10 - k`, `υ k = 1/(10 - k)`), `schurBud_le`, `exists_glPt` (`N = 2097152`, `κ = 1`, `τ = 1/10`, `z = i`), `interp_le`, `card_glPts_le`, and `gue_local_det` at the matched scale `N = Nsz sz0 n`, `H = Xmat 3 (sz0.L n) (sz0.W n) ω` (see the Repair section below).
- Registry: one owed line added after the `UNCoreC''` line; owed entries 154 to 155 (`regcount.py`); the pre-check exits 0 with `#assert_rbm_axioms` passing. The full `lake build` in the worktree does not contain the new module (the root import is the hub's step at merge); the module is covered by the module build, the fresh elaboration (0 output lines) and the pre-check.
- Not targets: `UNGUESchurTail` is a new owed pin kept as hypothesis (UN-10); `UNGUELocal` is reduced, not proved outright; `EigenInterlacing`, the C form and refuted pins are not used.
- Section (a) has no mistake that changes a statement or verdict; no `(a′)` is needed.

## (c) Verified Mathlib names (`#check` in `mathlib_names.sh` and `mn2.lean`: 27 of 27 names elaborate, 0 errors)
- `Real.rpow_natCast : ∀ (x : ℝ) (n : ℕ), x ^ ↑n = x ^ n`
- `Real.rpow_mul : 0 ≤ x → ∀ y z, x ^ (y * z) = (x ^ y) ^ z`
- `Real.rpow_neg : 0 ≤ x → ∀ y, x ^ (-y) = (x ^ y)⁻¹`
- `Real.rpow_sub : 0 < x → ∀ y z, x ^ (y - z) = x ^ y / x ^ z`
- `Real.le_sqrt_of_sq_le : x ^ 2 ≤ y → x ≤ √y`
- `Real.rpow_le_one_of_one_le_of_nonpos : 1 ≤ x → z ≤ 0 → x ^ z ≤ 1`
- `Matrix.isHermitian_zero : Matrix.IsHermitian 0`
- `Fintype.card_pos_iff : 0 < Fintype.card α ↔ Nonempty α`
- `Nat.floor_le : 0 ≤ a → ↑⌊a⌋₊ ≤ a`
- the other 18 names of the 27 are used in the file and elaborate: `Real.rpow_add`, `Real.rpow_one`, `Real.rpow_neg_one`, `Real.sqrt_eq_rpow`, `Real.rpow_le_rpow_of_exponent_le`, `Real.one_le_rpow`, `Matrix.nonsing_inv_eq_ringInverse`, `tendsto_natCast_atTop_atTop`, `tendsto_rpow_neg_atTop`, `tendsto_rpow_atTop`, `Nat.lt_floor_add_one`, `Nat.le_floor`, `Fintype.card_pos`, `Complex.norm_natCast`, `Finset.card_image_le`, `Real.sqrt_le_sqrt`, `Real.sqrt_le_iff`, `pow_le_pow_of_le_one`.
- Absent in RBM3D (replaced): `RBM.Gauss.norm_green_le` (no `theorem norm_green_le` in `RBM3D/`), `RBM.Gauss.isUnit_sub_smul_one_of_im_ne_zero` (the RBM3D name is `RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero`, `ConArgDet.lean:380`).

## (d) Open issues and paper-delta candidates
- `T2244a` (design, no paper statement): portmap row UN-09 (`T2162-portmap.md:203`) lists deps UN-01 only; by the imports (DECISIONS §54) it also needs `Green/LDE`, `Induction/ConArgDet`, `Induction/Split`, `Gauss/FlowCalculus` (all merged); RBM2D `norm_green_le` has no RBM3D twin (`norm_Gsig_le_inv_eta` plus the `Gres` bridge).
- `T2244b` (Lean-only, no paper statement): `GlSmall` is a conjunction `def`, not the RBM2D `structure` (same four fields, order of check 2.1).
- `T2244c` (doc): RBM2D's docstring says `GlSmall` from `N ≈ 10^73` at `κ = 1`, `τ = 1/10`; section (a) computes `log10 N = 72.09` (script in (a)); the Lean witness at `10^80` compiles.
- For UN-10 (owner of `UNGUESchurTail`): section (a)'s sanity run gives `max |Υ_i| / bud0 ≈ 3.6` at `N ≤ 2000` (flat in `N`) against `N^(1/40) = 1.2`; the pin is eventual in `n` at fixed `ε = 1/40`, so this is not a counterexample, but UN-10 must absorb the constant (`√log N`-type) into `N^ε`; nothing here tests the pin.
- Hub at merge: add `import RBM3D.Universality.GUELocalBootstrap` after the last `import` line of `RBM3D.lean`; `Axioms.lean` conflicts only in the lists (take the union; this branch adds one owed line at `:230`); then the full `lake build`.
- No statement differs from the ticket's pins; no new paper-delta beyond the three above.

## Repair (round 1 RETURN of `docs/reports/T2244-audit.md`; Tue Oct  6 03:06:01 UTC 2026)
Repairer model: claude-opus-5-5. Scope: audit items 1-3 only; one commit `23d9275` on `t/T2244`, file `RBM3D/Universality/GUELocalBootstrap.lean`, instance section only (no statement, definition or registry change).
```
$ git diff --stat 06eefc8 23d9275
 RBM3D/Universality/GUELocalBootstrap.lean | 132 +++++++++++++++++++++++++++---
 1 file changed, 119 insertions(+), 13 deletions(-)
$ lake build RBM3D.Universality.GUELocalBootstrap 2>&1 | tail -1
Build completed successfully (3367 jobs).
$ grep -nE "\bsorry\b|\badmit\b|^\s*axiom |native_decide" RBM3D/Universality/GUELocalBootstrap.lean
(no output)
$ grep -c "Xmat 3 4 32" RBM3D/Universality/GUELocalBootstrap.lean   (old gue_local_det example removed)
0
$ grep -c '^example' $F; per target: sed -n '/^namespace GUELocalBootstrapInst/,$p' $F | grep -cw <name>
examples in the file: 19
sc_stability 2 | norm_green_diag_le_two 2 | sc_one_step 2 | chain_bound 2 | exists_glPt 2 | gue_local_det 3
$ python3 exr.py   (new examples, statement extracted from the file; target applied)
example : ‖(msc Complex.I + 1 / 2) - msc Complex.I‖ ≤ 2 * ‖(msc Complex.I + 1 / 2) * (Complex.I + (msc Complex.I + 1 / 2)) + 1‖ / 1 :=
   applies: sc_stability | proof lines: 2
example : ‖green (0 : Matrix Unit Unit ℂ) ⟨0, 10⟩ () ()‖ ≤ 2 :=
   applies: norm_green_diag_le_two | proof lines: 3
example : ‖stieltjesN (0 : Matrix Unit Unit ℂ) ⟨0, 10⟩ - msc ⟨0, 10⟩‖ ≤ 4 * (1 / 10) / 10 :=
   applies: sc_one_step | proof lines: 4
example : ∀ k : ℕ, k ≤ 1 → ‖stieltjesN (0 : Matrix Unit Unit ℂ) ⟨0, 10 - (k : ℝ) * 1⟩ - msc ⟨0, 10 - (k : ℝ) * 1⟩‖ ≤ 4 * (1 / (10 - (k : ℝ) * 1)) / cGap 2 := by
   applies: chain_bound | proof lines: 13
example : ∃ j k : ℕ, j ≤ glJ (2097152 : ℝ) 1 ∧ k ≤ glK (2097152 : ℝ) (1 / 10) ∧ 0 ≤ Complex.I.re - glE 2097152 1 j ∧ Complex.I.re - glE 2097152 1 j ≤ glMesh 2097152 ∧ 0 ≤ glEta 2097152 k - Complex.I.im ∧ glEta 2097152 k - Complex.I.im ≤ glMesh 2097152 :=
   applies: exists_glPt | proof lines: 3
example (h : UNGUESchurTail) : ∀ᶠ n in atTop, ∃ ω : Ω 3 (sz0.L n) (sz0.W n), ∀ z : ℂ, |z.re| ≤ 2 - 1 → Nsz sz0 n ^ (-1 + 1 / 10 : ℝ) ≤ z.im → z.im ≤ 10 → ‖stieltjesN (Xmat 3 (sz0.L n) (sz0.W n) ω) z - msc z‖ ≤ Nsz sz0 n ^ (1 / 10 : ℝ) / Real.sqrt (Nsz sz0 n * z.im) := by
   applies: gue_local_det | proof lines: 20
$ lake env lean ax.lean   (the same six examples copied as named theorems ex_<target>, with the private helpers; #print axioms)
'RBM.Univ.GUELocalBootstrapInst.ex_sc_stability' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUELocalBootstrapInst.ex_norm_green_diag_le_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUELocalBootstrapInst.ex_sc_one_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUELocalBootstrapInst.ex_chain_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUELocalBootstrapInst.ex_exists_glPt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUELocalBootstrapInst.ex_gue_local_det' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
$ lake env lean pre.lean 2>&1 | grep -E "axiom audit|premises found|registry:|UNGUE" | cut -c1-110   (pre.lean: import RBM3D; import RBM3D.Universality.GUELocalBootstrap; #assert_rbm_axioms)
axiom audit: 7110 theorems, 2398 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.Univ.UNGUELocal: 41 [no certificate]
  RBM.Univ.UNGUESchurTail: 3 [no certificate]
premises found by scanning: 145 (borrowed 1, owed 106, structural 32, refuted 6).
registry: 2 borrowed + 155 owed + 91 structural + 7 refuted; 110 registered premise(s) carry nothing yet: [RBM
 RBM.Univ.UNGUELocal,
exit 0
```
- Item 1: every deterministic hypothesis is discharged. `H = 0` on `Unit` gives `G = -z⁻¹`, `m_N = -z⁻¹`, `Υ = -z⁻¹` (private helpers `GUELocalBootstrap_green_zero_unit`, `_stieltjesN_zero_unit`, `_schurErr_zero_unit`, `_norm_schurErr_zero_unit`: `‖Υ(⟨0, η⟩)‖ = 1/η`). `‖m_N − m_sc‖ ≤ 1/10 + 1/10` at `z = 10i` (`GUELocalBootstrap_near_zero_unit`). `cGap 2 = 2` (`GUELocalBootstrap_cGap_two`). `chain_bound` step `k = 0`: `4(1/10)/2 + 2/(10·9) ≤ min 1 (1/4)` by `norm_num`.
- Item 2: `gue_local_det` is applied at `N = Nsz sz0 n`, the matrix `Xmat 3 (sz0.L n) (sz0.W n) ω`, `κ = 1`, `τ = 1/10`, with `GlSmall` from `inst_glSmall`. `hΓ` is not a hypothesis. It holds at an `ω` outside the event of `inst_schurTail h`, whose measure is at most `ofReal (N^{-2}) < 1` (since `55 ≤ N` by `GlSmall`). `UNGUESchurTail` (UN-10's pin) is the only hypothesis kept. `Nonempty (Idx 3 …)` is a local `have` (`⟨0⟩`).
- (c) additions (the module builds with each name): `ENNReal.ofReal_lt_one`, `Real.rpow_lt_one_of_one_lt_of_neg`, `Set.ne_univ_iff_exists_notMem`, `Set.mem_ofPred_eq` (`Set.mem_setOf_eq` is deprecated), `MeasureTheory.measure_univ`, `Matrix.inv_eq_left_inv`, `Real.sqrt_sq`, `Complex.norm_I`, `Complex.norm_real`, `Complex.I_im`, `div_le_div_iff₀`.
