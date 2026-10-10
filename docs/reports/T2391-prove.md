Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct 10 21:35:47 UTC 2026

Setting (BA data, as `baSig_decay` `KPure.lean:632` and `baSig_signed_sum` `KSumZeroA.lean:1079`): `ι` a family of data `(L i, g i, E i, m i, t i)`; `3 ≤ d`, `3 ≤ n`, `Λ > 0`, `κ > 0`, `3 ≤ L i`, `0 < g i ≤ Λ`, `BAReal d (L i) (g i) κ (E i) (m i)`, `0 ≤ t i` (and `t i < 1` where stated). `M(σ) = BAMsigma (BAMB ..)`, `Σ^{(∅)} = BASig`. All constants depend on `(d, n, Λ, κ)` (and `Q` for B3) only, never on `i`. Targets in mathematics:
- **B1** (any `F` with `KLIsTSP F`, `2 ≤ n`, any labelling `β` of the `n + 2|F|` slots by `Z_L^d` with `v ↦ β(leaf v)` non-constant; no `σ`, `t`, `g`): either some chord `J ∈ F` has `β(In J) ≠ β(Out J)`, or there are two distinct slots `s ≠ s'` with `β(s) ≠ β(next s)` and `β(s') ≠ β(next s')`.
- **B2** (`baSig_nc_pointwise`; every `σ`, `0 ≤ t i ≤ 1`): `∃ G, c > 0`, `∀ i σ δ`, `δ` non-constant: `‖BASig i σ δ‖ ≤ G (g i)² e^{-c·maxDist δ}`.
- **B3** (`baSig_weighted`; `0 ≤ t i < 1`, every `Q : ℕ`): `∃ C > 0`, `∀ i`, alternating `σ`, `r`, `x`: `Σ_{δ_r = x} ‖BASig i σ δ‖ (maxDist δ + 1)^Q ≤ C ((g i)² + 1 − t i)`; `C = C_Q`-type, `C_Q = 2^Q (1 + Q!/(c/2)^Q)`.
- **B4** (`baSig_sumZeroAbs`): `SigSumZeroAbs d n L g t (BASig d n L g E m t)` under `3 ≤ d`, `3 ≤ n`, `Λ, κ > 0`, `3 ≤ L i`, `0 < g i ≤ Λ`, `BAReal`, `0 ≤ t i`, `t i < 1`. The ticket lists only `3 ≤ n`, `t i < 1`, `BAReal`, `g i ≤ Λ`; the other hypotheses are the same as `baSig_signed_sum` (needed by `baPure_edge`, `baSig_signed_sum`), so the statement carries them: an abbreviation in the ticket, not a defect. Clauses 1-2: `baSig_transl`; clause 3 (for each `Q ≤ 2(d−1)`): `‖Σ_{δ_r=x}‖ ≤ C₁(1−t)` from `baSig_signed_sum`, and the weighted bound from B3, with `C = max(C₁, C_Q-constant)`.

### (i) Exponent table
| # | quantity | value / instance | constraint | slack |
|---|---|---|---|---|
| 1 | `d` | 3 | `3 ≤ d` (`baPure_edge`, `baSig_signed_sum`); `2 ≤ d` for `baSigmaTree_bound` | 0 / 1 |
| 2 | `n` | 4 (alternating forces `n` even `≥ 4`) | `3 ≤ n` (`baSig_signed_sum`); `2 ≤ n` (`baSlot_path_le`, `baSigmaTree_bound`); `SigSumZeroAbs` alone is false at `n = 2` (T2385b) | 1 |
| 3 | `t` | `1/2`, `999/1000` | `0 ≤ t ≤ 1` for B2 (`baPure_edge`, `‖tΘ‖ ≤ ‖Θ‖`); `t < 1` for B3, B4 (signed clause of K08a) | `1−t = 1/2`, `1/1000` |
| 4 | `g²` gain | exponent 2 | B1: one off-diagonal chord (`‖tΘ^{(s,s)}_{xy}‖ ≤ C₅ g² e^{-c_s|x−y|}`, `x ≠ y`, `baProp5s_of_real`) or two off-diagonal `M`-edges (`‖M_{xy}‖² = K_{xy} ≤ A g² e^{-2c₀|x−y|}`, so each `≤ A^{1/2} g e^{-c₀|x−y|}`, `BAK_off_le`) | 0 (tight: one `M`-edge alone gives only `g`; B1 needs two) |
| 5 | edge prefactor `B'` | `B' = max(baPureB, C₅, A^{1/2}) ≥ 1` (any `B' ≥ 1` with these three bounds) | every edge `≤ B' e^{-r|x−y|}`; the distinguished edges give an extra `g²` (chord) or `g·g` (two `M`-edges); `Γ = B'^{n+3n²}`, `#edges = n + 3|F| ≤ n + 3n²` | — |
| 6 | edge rate `r` | `r = min(min(c₀, log 2), c_s) = 9.0e-32` (numbers below; `r ≤ c₀`, `r ≤ c_s`) | `r ≤ c₀` for `M`-edges, `r ≤ c_s` for chords: the extracted `g²` edge still has rate `≥ r` | 0 (`r = c_s`) |
| 7 | B2 rate `c` | `c = r/4` (`baSigmaTree_bound`, pair `(i,j)` realising `maxDist`, `KLMolecule_exists_pair`) | `c > 0` | — |
| 8 | B2 constant `G` | `G = |TSP n| · Γ · S₀^{N₀}`, `N₀ = n + 2n² = 36`, `S₀ = expC(d−2, r/(4N₀))` | sum over trees of `KLTSPlong n σ ∅ ⊆ TSP n`, all chords short (`KLMolecule_same_charge`) | — |
| 9 | B3 `Q` | every `Q ∈ ℕ`; `SigSumZeroAbs` needs `Q ≤ 2(d−1) = 4` | `C_Q = 2^Q (1 + Q!/(c/2)^Q) < ∞` for all `Q` (`(M+1)^Q e^{-cM} ≤ C_Q e^{-(c/2)M}`) | any `Q` |
| 10 | B3 slice sum | `Σ_{δ_r=x} e^{-(c/2) maxDist} ≤ expC(d−2, (c/2)/n)^{n−1}` | translation of `δ` (`KLIndStepA_maxDist_add_const`, `KLIndStepA_sum_slice_root`) + `KLMolecule_sum_exp_maxDist` (all merged, public) | — |
| 11 | B3 constant | `R = G C_Q expC(d−2,(c/2)/n)^{n−1}`; `C = C₁ + 2R + 1` | non-constant part `≤ g² R`; constant `δ ≡ x`: `‖Σ(c₀)‖ ≤ ‖Σ_slice‖ + Σ_{nonconst}‖Σ‖ ≤ C₁(1−t) + g² R`; total `≤ (C₁ + 2R + 1)(g² + 1 − t)` | 0 (the band arithmetic of `KLsumZero_weighted`, `KLIndStepA.lean:941-1000`) |
| 12 | decay `(1−t)` | 1 power | signed clause `C₁(1−t)` is K08a's (`baSig_signed_sum`, `t i < 1`): `1 − 1 = 0` extra loss | 0 |

Numbers of rows 5-11 at `(d, Λ, κ, n, Q) = (3, 10, 0.560680, 4, 4)` (definitions of `BAct_C`, `BAct_rate`, `BAp5s_A/_S/_rate/_C`, `baPureB`, `baPureRate`, `expC` transcribed from `CombesThomas.lean:42-45`, `Prop5Short.lean:49-62`, `KPure.lean:105-111`, `RadialSum.lean:271`). Command: `cd $S/T2391 && python3 consts.py` (`S` = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/60e5425b-ae97-4201-b2dc-fc981af93073/scratchpad`). Output verbatim:
```
BAct_C=817 BAct_rate c0=0.00466145 (kappa/2=0.2803) A=1.229e+11 S=1.301e+13
c_s=BAp5s_rate=9.004e-32 C5=6.588e+27 baPureB=6.654e+29 baPureRate r=9.004e-32  r<=c0:True r<=log2:True r<=c_s:True
B2 rate c=r/4=2.251e-32; #edges <= n+3n^2=52; N0=n+2n^2=36; baSigmaTree lam=r/(4 N0)=6.252e-34
B3: c/2=1.125e-32; C_Q (Q=4) = 2^Q(1+Q!/(c/2)^Q) = 2.394e+130; Q range 0..2(d-1)=4; expC(d-2,(c/2)/n)=9.804e+133
```
These huge values are the constants of the conclusions (`∃ G c`, `∃ C`), not hypotheses of any target; no hypothesis depends on them. The numerics of (ii) show the actual ratios are `O(1)`.

Proof of B1 (argument as in T2385 (a+) B1; checked below). Suppose every chord has equal ends and at most one slot `s*` has `β(s*) ≠ β(next s*)`. If such `s*` exists, `BAnextSlot_orbit` (`KCactus.lean:403`) gives `k` with `next^k(next s*) = s*`; take the first `i` with `next^i(next s*) = s*`; the edges along `next s*, …, next^{i−1}(next s*)` start at slots `≠ s*`, so all are equal and `β(next s*) = β(s*)`, a contradiction. So every `M`-edge and every chord has equal ends, the total length `T(β) = 0`, `baSlot_path_le` (`KPure.lean:377`) gives `β` constant, and `v ↦ β(leaf v) = δ v` is constant, contradicting the hypothesis.
Proof of B2. Layer `∅`: every chord of every tree has `σ_i = σ_j` (`KLMolecule_same_charge`), so every edge `≤ B' e^{-r|x−y|}` (`baPure_edge` (a), (c)). For `β` consistent with a non-constant `δ`, B1 gives a chord (use `baProp5s_of_real` for `x ≠ y`, `‖tΘ‖ ≤ ‖Θ‖`) or two distinct `M`-edges (use `BAK_off_le` in square-root form, for both charges since `M(−) = Mᴴ` and `|x−y|` is symmetric) with extra factor `g²`; so `∏‖edge‖ ≤ Γ g² e^{-r T(β)}`: the `hprod` hypothesis of `baSigmaTree_bound` (`KPure.lean:414`) at every `β` with `β(leaf v) = δ v`. It gives `‖Σ_F(δ)‖ ≤ Γ g² S₀^{N₀} e^{-(r/4)|δ_i−δ_j|}`; sum over `F`. No alternation and no `t < 1` is used.

### (ii) One concrete nondegenerate instance
Flow point `P` of `(d, L, g) = (3, 4, 10)` (`MFixedPoint.lean:849-893`: `w = 6i/5`, `m_S = L^{-3} tr(gΨ − w)^{-1}`, `z_S = w − m_S`, `t₀ = Im m_S/(Im m_S + Im z_S)`, `E = BAflowE`, `m₀ = m_S/√t₀`, `g₀ = √t₀ g`), `Λ = 10`, `κ = Im m₀`, `n = 4`, `σ = (+,−,+,−) = KLsigAlt 4` (alternating) and, for B2, `σ' = (+,+,−,+)` (not alternating, not constant: its chord `(0,2)` is long, `(1,3)` short); family `ι = {t = 1/2, t = 999/1000}`. The script builds `M = (g₀Ψ − E − m₀)^{-1}` on `Z_4³` (64 sites) and `Σ^{(∅)}` as the sum of the cactus weights of the trees of `TSP 4` with no long chord, on the slice `δ_0 = 0`. Command: `cd $S/T2391 && python3 inst_B.py`. Output verbatim:
```
hyps: 3<=d True  3<=L True  Lam>0 True  kappa=Im m0=0.560680>0 True  0<g0=4.672337<=Lam True  BASelf resid=3.3e-16<1e-12 True  kappa<=Im m0 True
n=4 3<=n True; slice delta_0=0 has 262144 entries, 262143 nonconstant, constant delta = 1; max maxDist = 6
  sigma=(+,-,+,-) t=0.5    alt=True  nonzero=262144/262144 |signed|/(1-t)=2.1165 absQ/(g0^2+1-t) Q=0..4: 0.456 2.548 14.903 90.405 565.268
     max over nonconstant delta of |Sigma|/g0^2 by maxDist m -> 1:7.48e-06 2:9.37e-05 3:1.13e-06 4:9.29e-05 5:2.23e-06 6:2.30e-03
  sigma=(+,+,-,+) t=0.5    alt=False nonzero=262144/262144 absQ/(g0^2+1-t) Q=0..4: 0.523 2.962 17.581 108.191 685.348
     max over nonconstant delta of |Sigma|/g0^2 by maxDist m -> 1:8.62e-06 2:1.75e-04 3:1.14e-06 4:1.74e-04 5:2.00e-06 6:3.38e-03
  sigma=(+,-,+,-) t=0.999  alt=True  nonzero=262144/262144 |signed|/(1-t)=1.5913 absQ/(g0^2+1-t) Q=0..4: 0.386 2.113 12.058 71.342 435.704
     max over nonconstant delta of |Sigma|/g0^2 by maxDist m -> 1:6.76e-06 2:4.97e-05 3:1.12e-06 4:4.87e-05 5:2.52e-06 6:1.01e-03
  sigma=(+,+,-,+) t=0.999  alt=False nonzero=262144/262144 absQ/(g0^2+1-t) Q=0..4: 0.494 2.779 16.364 99.924 628.570
     max over nonconstant delta of |Sigma|/g0^2 by maxDist m -> 1:8.63e-06 2:1.72e-04 3:1.14e-06 4:1.71e-04 5:2.14e-06 6:2.74e-03
```
All hypotheses hold at once: `3 ≤ d`, `3 ≤ n`, `3 ≤ L = 4`, `0 < g₀ = 4.672 ≤ Λ = 10`, `κ = Im m₀ = 0.5607 > 0`, `BASelf` residual `3.3e-16`, `0 ≤ t < 1`. Nondegenerate: all 262144 slice entries are nonzero, 262143 are non-constant `δ` (so B2 and the weighted sum are not vacuous), the signed slice sum is nonzero (`|·|/(1−t) = 2.12` at `t = 1/2`, `1.59` at `t = 0.999`), `Q` runs over `0..4 = 0..2(d−1)`, two different `t` (one near 1). The ratios `|signed|/(1−t)` and `absQ/(g₀²+1−t)` are `O(1)` at `t = 0.999` (no growth as `1−t ↓`).
Uniformity in `g` (B2, B3): command `cd $S/T2391 && python3 gscan.py` (`E = 0.3`, `t = 0.999`, `σ = (+,−,+,−)`). Output verbatim:
```
d=3 L=4 n=4 t=0.999 E=0.3 sigma=(+,-,+,-); columns: g, Im m, max_nonconst |Sigma|/g^2, sum_nonconst |Sigma|(maxDist+1)^2/g^2, |signed slice|/(1-t), |Sigma(const)|/(g^2+1-t)
g=0.015625  Im m=0.9880     0.2550     13.0385    0.5125    1.0096
g=0.125     Im m=0.9480     0.2034     96.9446    0.5566    2.2289
g=1         Im m=0.5723     0.0235    495.3580    1.5270    0.0471
g=10        Im m=0.5388     0.0002      2.5802    1.7229    0.0002
```
(`max_nonconst |Σ|/g²` and `Σ_nonconst |Σ|(maxDist+1)²/g²` stay bounded as `g ↓ 1/64`: the `g²` factor of B2/B3 is visible; `L = 4` is too small to show the `e^{-c·maxDist}` decay.)
B1 brute force (3 labels, all trees of `TSP n`, slot cycles as in `KCactus.lean:100-150, 347`: slots per node sorted by `BAslotStart`, leaf `v` start `v`, child side of `J` start `J.1`, parent side start `J.2`). Commands: `cd $S/T2391 && python3 b1.py; python3 b1b.py`. Output verbatim:
```
n=4 labels in 0..2: (#trees, #labellings with nonconstant leaf labels, #violating B1) = (3, 1482, 0)
n=5 labels in 0..2: (#trees, #labellings with nonconstant leaf labels, #violating B1) = (11, 108240, 0)
n=6 labels in 0..2: (#trees, #labellings with nonconstant leaf labels, #violating B1) = (45, 8704014, 0)
n=4: labellings with nonconstant leaves and all chords equal: 546 ; of these with max unequal M-edges in a cycle = 2: 312 ; with a cycle having exactly 1 unequal M-edge: 0
```
No labelling violates B1; the second clause is needed (546 labellings have all chords equal) and "two" is sharp and never "one" (312 have exactly two unequal `M`-edges in a cycle, none exactly one).
External hypotheses: none. B2, B3, B4 use only merged theorems (`baPure_edge`, `baProp5s_of_real`, `BAK_off_le`, `baSigmaTree_bound`, `baSlot_path_le`, `BAnextSlot_orbit`, `baSig_transl`, `baSig_signed_sum`, `KLMolecule_*`); no pin stays a hypothesis, so no limit computation (TEAM §8 lesson 14) is owed. Registry: B4 concludes the only predicate (`SigSumZeroAbs`) and no other Prop-valued premise is introduced; nothing to bridge.

### Verdict
- **B1 (combinatorics): PASS** (proof above; brute-force check, 0 violations; hypotheses `KLIsTSP F`, `2 ≤ n` only).
- **B2 (`baSig_nc_pointwise`): PASS** (every edge of layer `∅` is `≤ B' e^{-r|·|}`; B1 supplies the `g²`; uniform in `(L, g, E, m, t)`; rates `r ≤ c₀, c_s`).
- **B3 (`baSig_weighted`, every `Q`): PASS** (band arithmetic of `KLsumZero_weighted` with B2 and K08a's signed clause; the band helpers `KLIndStepA_poly_exp`, `KLIndStepA_sum_exp_root`, `KLIndStepA_pow_le` are `private` in `Loop/KLIndStepA.lean`, so stage 1b re-proves them as `private` `KSumZeroB_` lemmas; the public `KLIndStepA_sum_slice_root`, `KLIndStepA_maxDist_add_const`, `KLMolecule_sum_exp_maxDist` are usable).
- **B4 (`baSig_sumZeroAbs`): PASS** under the full hypothesis list above (`SigSumZeroAbs` untouched; `3 ≤ n`, `t i < 1` as in `sigSumZeroAbs_band`).
- **Instances (ticket target 5): PASS** (all hypotheses hold at once at `P`, `Λ = 10`, `κ = Im m₀`, `n = 4`, `σ = KLsigAlt 4`, `t ∈ {1/2, 999/1000}`; not `t = 0`, not a constant `δ` only).
## (b) Script output (stage 1b; times by `date -u`, Sat Oct 10 2026; scripts in `$S/T2391`, `S` as in (a)(ii))
**Line count against the stop line: `wc -l RBM3D/BA/KSumZeroB.lean` = 755; stop line 2,000 (binding), not reached** ((a+)(iii) estimate of K08b: 720 / 990 / 1520). All commands ran in the worktree `RBM3D-wt/T2391` at commit `205ffb5`, `git status --short` empty.
```
$ git log --format='%h %s' main..t/T2391
205ffb5 T2391: KSumZeroB docstrings and section headers
82536e5 T2391: KSumZeroB instances at the flow point P (B1-B4), docstring line numbers
cd9dfdd T2391: KSumZeroB sections 4-5 (B3 baSig_weighted, B4 baSig_sumZeroAbs)
8d6290b T2391: KSumZeroB section 3 (B2, baSig_nc_pointwise: the pointwise g^2 bound for a non-constant delta)
37dbf01 T2391: KSumZeroB section 2 (the product of the edge entries with the gain g^2)
4992887 T2391: KSumZeroB section 1 (B1, an unequal edge in every non-constant cactus labelling)
$ git diff --stat main...t/T2391
 RBM3D/BA/KSumZeroB.lean | 755 ++++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 755 insertions(+)
$ for c in the six commits: git show $c:RBM3D/BA/KSumZeroB.lean | wc -l
4992887 117
37dbf01 232
8d6290b 452
cd9dfdd 622
82536e5 752
205ffb5 755
$ lake build RBM3D.BA.KSumZeroB 2>&1 | tail -1                     # 22:02:37 UTC (HEAD 205ffb5, git status empty)
Build completed successfully (3774 jobs).
$ grep 'Built RBM3D.BA.KSumZeroB' bld.log; grep -c 'KSumZeroB.lean:' bld.log   # log of the last rebuild of the module, file time 21:56:32 UTC
✔ [3774/3774] Built RBM3D.BA.KSumZeroB (4.3s)
0
$ lake build   # 21:58:09 to 21:58:47 UTC; `import RBM3D.BA.KSumZeroB` added to RBM3D.lean after the last import, then RBM3D.lean restored (git status empty)
exit=0   RBM3D.lean:437:0: axiom audit: 11211 theorems, 3356 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4205 jobs).
$ lake env lean docs/tickets/checks/T2391-check.lean                 # 21:57:13 UTC
exit=0   14 `#check` outputs, 0 error lines
$ lake env lean reg.lean    # `import RBM3D`, `import RBM3D.BA.KSumZeroB`, `#assert_rbm_axioms` (registry pre-check)
exit=0
axiom audit: 11211 theorems, 3356 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.   (wrapped lines joined)
$ #print axioms of the four public declarations                # 21:57:53 UTC
'RBM.BA.KSumZeroB_unequal_edge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSig_nc_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSig_weighted' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSig_sumZeroAbs' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -n 'sorry\|admit\|native_decide\|axiom' RBM3D/BA/KSumZeroB.lean | wc -l
0
```
Target statements, extracted from the file by script (`theorem NAME` up to `:= by`, whitespace normalised). The script also compares the binder lists with the merged siblings (`baSig_decay`, `KPure.lean:632`; `baSig_signed_sum`, `KSumZeroA.lean:1079`) and the conclusion of B4 with the pin `SigSumZeroAbs d n L g t (BASig d n L g E m t)`:
```
theorem KSumZeroB_unequal_edge {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n) (β : BAslot F → Zd d L) (hnc : ∃ v w : Fin n, β (BAslotLeaf F v) ≠ β (BAslotLeaf F w)) : (∃ J : ↥F, β (BAslotIn F J) ≠ β (BAslotOut F J)) ∨ ∃ s s' : BAslot F, s ≠ s' ∧ BAslotNode F s = BAslotNode F s' ∧ β s ≠ β (BAnextSlot F s) ∧ β s' ≠ β (BAnextSlot F s')
theorem baSig_nc_pointwise {ι : Type} {d n : ℕ} [NeZero n] (hd : 3 ≤ d) (hn : 2 ≤ n) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) (L : ι → ℕ) [∀ i, NeZero (L i)] (g E : ι → ℝ) (m : ι → ℂ) (t : ι → ℝ) (hL : ∀ i, 3 ≤ L i) (hg : ∀ i, 0 < g i) (hgΛ : ∀ i, g i ≤ Λ) (hr : ∀ i, BAReal d (L i) (g i) κ (E i) (m i)) (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1) : ∃ G : ℝ, 0 < G ∧ ∃ c : ℝ, 0 < c ∧ ∀ (i : ι) (σ : Fin n → Bool) (δ : Fin n → Zd d (L i)), (∃ v w : Fin n, δ v ≠ δ w) → ‖BASig d n L g E m t i σ δ‖ ≤ G * g i ^ 2 * Real.exp (-(c * (KLmaxDist d (L i) δ : ℝ)))
theorem baSig_weighted {ι : Type} {d n : ℕ} [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) (L : ι → ℕ) [∀ i, NeZero (L i)] (g E : ι → ℝ) (m : ι → ℂ) (t : ι → ℝ) (hL : ∀ i, 3 ≤ L i) (hg : ∀ i, 0 < g i) (hgΛ : ∀ i, g i ≤ Λ) (hr : ∀ i, BAReal d (L i) (g i) κ (E i) (m i)) (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i < 1) (Q : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (i : ι) (σ : Fin n → Bool), (∀ j, σ j ≠ σ (j + 1)) → ∀ (r : Fin n) (x : Zd d (L i)), ∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d (L i) => δ r = x), ‖BASig d n L g E m t i σ δ‖ * ((KLmaxDist d (L i) δ : ℝ) + 1) ^ Q ≤ C * (g i ^ 2 + (1 - t i))
theorem baSig_sumZeroAbs {ι : Type} {d n : ℕ} [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) (L : ι → ℕ) [∀ i, NeZero (L i)] (g E : ι → ℝ) (m : ι → ℂ) (t : ι → ℝ) (hL : ∀ i, 3 ≤ L i) (hg : ∀ i, 0 < g i) (hgΛ : ∀ i, g i ≤ Λ) (hr : ∀ i, BAReal d (L i) (g i) κ (E i) (m i)) (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i < 1) : SigSumZeroAbs d n L g t (BASig d n L g E m t)
B2 binders == baSig_decay binders with (hn : 3 ≤ n) -> (hn : 2 ≤ n): True
B3 binders == baSig_signed_sum binders + (Q : ℕ): True
B4 binders == baSig_signed_sum binders: True
B4 conclusion: SigSumZeroAbs d n L g t (BASig d n L g E m t)
pin SigSumZeroAbs d n L g t (BASig d n L g E m t) identical to B4 conclusion: True
```
Compiled nonempty instances (10 `example`s of `namespace RBM.BA.KSumZeroBInst`, extracted by script: the statement, or the head of the application term; data = the merged flow point `P` of `(3,4)`, `Λ = 10`, `κ = P.m0.im`, `P.real`, `P.g0_pos`, `P.g0_le`; `KSumZeroB_nc = (0,0,0,e₁)` is not constant; no hypothesis of another gate remains):
```
[1] example := KSumZeroB_unequal_edge (d := 3) (L := 4) (n := 4) (F := {((0 : Fin 4), (2 : Fin 4))}) KSumZeroB_F02 (by norm_num) (Sum.elim KSumZeroB_nc (fun _ => 0)) KSumZeroB_nc_nonconst ...
[2] example : ∃ s s' : BAslot ({((0 : Fin 4), (2 : Fin 4))} : Finset (Fin 4 × Fin 4)), s ≠ s' ∧ BAslotNode ({((0 : Fin 4), (2 : Fin 4))} : Finset (Fin 4 × Fin 4)) s = BAslotNode ({((0 : Fin 4), (2 : Fin 4))} : Finset (Fin 4 × Fin 4)) s' ∧ (Sum.elim KSumZeroB_nc (fun _ => (0 : Zd 3 4)) : BAslot ({((0 : Fin 4), (2 : Fin 4))} : Finset (Fin 4 × Fin 4)) → Zd 3 4) s ≠ Sum.elim KSumZeroB_nc (fun _ => (0 : Zd 3 4)) (BAnextSlot ({((0 : Fin 4), (2 : Fin 4))} : Finset (Fin 4 × Fin 4)) s) ∧ Sum.elim KSumZeroB_nc (fun _ => (0 : Zd 3 4)) s' ≠ Sum.elim KSumZeroB_nc (fun _ => (0 : Zd 3 4)) (BAnextSlot ({((0 : Fin 4), (2 : Fin 4))} : Finset (Fin 4 × Fin 4)) s')
[3] example : ∃ G : ℝ, 0 < G ∧ ∃ c : ℝ, 0 < c ∧ ‖BASig 3 4 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => (1 : ℝ) / 2) () (KLsigAlt 4) KSumZeroB_nc‖ ≤ G * P.g0 ^ 2 * Real.exp (-(c * (KLmaxDist 3 4 KSumZeroB_nc : ℝ)))
[4] example : ∃ G : ℝ, 0 < G ∧ ∃ c : ℝ, 0 < c ∧ ‖BASig 3 4 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => (999 : ℝ) / 1000) () (KLsigAlt 4) KSumZeroB_nc‖ ≤ G * P.g0 ^ 2 * Real.exp (-(c * (KLmaxDist 3 4 KSumZeroB_nc : ℝ)))
[5] example : ∃ G : ℝ, 0 < G ∧ ∃ c : ℝ, 0 < c ∧ ‖BASig 3 4 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => (1 : ℝ) / 2) () (fun v : Fin 4 => decide (v ≠ 2)) KSumZeroB_nc‖ ≤ G * P.g0 ^ 2 * Real.exp (-(c * (KLmaxDist 3 4 KSumZeroB_nc : ℝ)))
[6] example : ∃ C : ℝ, 0 < C ∧ ∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 4 => δ 0 = 0), ‖BASig 3 4 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => (1 : ℝ) / 2) () (KLsigAlt 4) δ‖ * ((KLmaxDist 3 4 δ : ℝ) + 1) ^ 4 ≤ C * (P.g0 ^ 2 + (1 - 1 / 2))
[7] example : ∃ C : ℝ, 0 < C ∧ ∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 4 => δ 3 = fun j => if j = 0 then 1 else 0), ‖BASig 3 4 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => (999 : ℝ) / 1000) () (KLsigAlt 4) δ‖ * ((KLmaxDist 3 4 δ : ℝ) + 1) ^ 4 ≤ C * (P.g0 ^ 2 + (1 - 999 / 1000))
[8] example : ∃ C : ℝ, 0 < C ∧ ∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 4 => δ 1 = 0), ‖BASig 3 4 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => (1 : ℝ) / 2) () (fun k => !KLsigAlt 4 k) δ‖ * ((KLmaxDist 3 4 δ : ℝ) + 1) ^ 2 ≤ C * (P.g0 ^ 2 + (1 - 1 / 2))
[9] example : SigSumZeroAbs 3 4 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => (999 : ℝ) / 1000) (BASig 3 4 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => (999 : ℝ) / 1000))
[10] example : ∃ C : ℝ, 0 < C ∧ ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 4 => δ 0 = 0), BASig 3 4 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => (1 : ℝ) / 2) () (KLsigAlt 4) δ‖ ≤ C * (1 - 1 / 2) ∧ ∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 4 => δ 0 = 0), ‖BASig 3 4 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => (1 : ℝ) / 2) () (KLsigAlt 4) δ‖ * ((KLmaxDist 3 4 δ : ℝ) + 1) ^ 4 ≤ C * (P.g0 ^ 2 + (1 - 1 / 2))
```
Declaration index (line name; script `decls.py`): 50 KSumZeroB_cycle (private); 87 KSumZeroB_unequal_edge (public); 124 KSumZeroB_prod_gain (private); 151 KSumZeroB_prod_exp (private); 162 KSumZeroB_card_edges (private); 173 KSumZeroB_prod_le (private); 241 KSumZeroB_theta_shift (private); 261 KSumZeroB_norm_sigma (private); 272 KSumZeroB_chord_off (private); 308 KSumZeroB_M_off (private); 341 KSumZeroB_tree_bound (private); 378 baSig_nc_pointwise (public); 464 KSumZeroB_pow_le (private); 479 KSumZeroB_poly_exp (private); 502 KSumZeroB_sum_exp_root (private); 515 KSumZeroB_weighted_of (private); 584 baSig_weighted (public); 610 baSig_sumZeroAbs (public); 637 KSumZeroB_nc (private); 639 KSumZeroB_nc_nonconst (private); 642 KSumZeroB_F02 (private)
Name-clash grep (22:02:03 UTC) of the four public names and of the stem `KSumZeroB` over `RBM3D/` and `RBM3D.lean`, own file excluded: 0 hits in the worktree (HEAD `205ffb5`) and 0 hits in the main worktree (HEAD `699d51b`).
Ports: none from `../RBM1D`, `../RBM2D` (nothing under them was opened, tool log); no diff-stat applies. Six private helpers of merged RBM3D files were copied in place (private there): `KPure_theta_shift` (`KPure.lean:71`), `KPure_prod_const_exp` (`:399`), `KInduct_norm_sigma` (`KInduct.lean:156`), `KLIndStepA_pow_le`, `_poly_exp`, `_sum_exp_root` (`KLIndStepA.lean:516, 859, 881`).

**Narrative.**
- Delivered: `RBM3D/BA/KSumZeroB.lean` (755 lines, namespace `RBM.BA`): four public theorems (B1 `KSumZeroB_unequal_edge`, B2 `baSig_nc_pointwise`, B3 `baSig_weighted`, B4 `baSig_sumZeroAbs`), 17 private declarations with the stem `KSumZeroB_`, 10 `example`s (index and list above). The branch diff touches only this file. `RBM3D.lean` is not edited on the branch (CLAUDE.md §1, §3 (A) step 4: the hub adds the import at merge); the full `lake build` with that import line added temporarily passes (above).
- The argument of (a) and of T2385 (a+) is implemented as written, with no external input and no open pin. B1: `KSumZeroB_cycle` (`Nat.find` on the first return of `BAnextSlot` to `s`), `BAnextSlot_orbit`, then `baSlot_path_le`. B2: `KSumZeroB_prod_le` (the product of the edge entries with the gain `g²`, from an unequal chord or two unequal `M`-edges) is the `hprod` of `baSigmaTree_bound`; entries from `baPure_edge`, `baProp5s_of_real` (chord, `x ≠ y`, no `1_{a=0}` term) and `BAK_off_le` (`M`-edge, `x ≠ y`, square root); prefactor `B = max (baPureB d Λ κ) (sqrt (BAp5s_A d Λ κ))` (`BAp5s_C ≤ baPureB`), rate `baPureRate`. B3: the slice arithmetic of `KLsumZero_weighted` as the abstract `KSumZeroB_weighted_of`, instanced at `BASig` with `baSig_signed_sum` (K08a) and B2. B4: `baSig_transl`, `baSig_signed_sum` and B3 with the constant `max C₁ C₂`.
- Differences from the text of (a), none a weakening: (1) B1 puts the two unequal `M`-edges in one node (stronger than "two distinct slots"); (2) B2 carries `hn : 2 ≤ n` (the setting of (a) says `3 ≤ n`; the binder script shows the list of `baSig_decay` otherwise, with `t i ≤ 1`): its proof needs only `2 ≤ n`; (3) B3 is the one weighted clause (ticket target 3), the signed clause is `baSig_signed_sum`; (4) B4 carries the hypothesis list of `baSig_signed_sum`, as (a) said. No hypothesis was added, no target weakened, no pin changed (`SigSumZeroAbs`, `baSig_decay`, `baSig_signed_sum` are untouched), no scope widened; no obstruction, no REQ trigger. Section (a) needs no correction: no (a′).
- Instances: [1]-[2] B1 at the tree `{(0,2)}` (6 slots, one chord) with non-constant leaf labels `δ₀`; [2] derives the second disjunct (the chord has equal ends, by `decide`); [3]-[5] B2 at `t = 1/2` and `999/1000` (alternating `σ`) and at `σ = (+,+,-,+)`; [6]-[8] B3 at `Q = 4 = 2(d-1)` (`t = 1/2`; `t = 999/1000`, root 3, label `e₁`) and `Q = 2` with the complementary alternating vector; [9]-[10] B4: the whole predicate at `t = 999/1000`, its third conjunct at `Q = 4`, `t = 1/2`. `n = 4` is the least admissible (alternating). Not `t = 0`; not a constant `δ` only (B2 at the non-constant `δ₀`; the B3 slice `δ_0 = 0` has 262143 non-constant points, (a)(ii)).
- Q4 line: K08b is 755 lines against (a+)(iii) 720 / 990 / 1520; K08a 1195 (`wc -l RBM3D/BA/KSumZeroA.lean`) + K08b 755 = 1950 against the 4.8k line.

## (c) Verified Mathlib names
`#check` on 96 core and Mathlib names used in the file (scratch file `chk_names.lean` importing `RBM3D.BA.KSumZeroB`, 22:03:21 UTC): 0 errors. Complex.norm_conj, Complex.norm_real, Complex.star_def, Equiv.addRight, Equiv.coe_addRight, Finset.add_sum_erase, Finset.card_le_card, Finset.card_le_univ, Finset.card_pos, Finset.card_univ, Finset.erase_subset, Finset.filter_subset, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, Finset.mul_prod_erase, Finset.mul_sum, Finset.prod_const, Finset.prod_le_prod₀, Finset.prod_mul_distrib, Finset.prod_nonneg, Finset.sum_congr, Finset.sum_const, Finset.sum_eq_zero, Finset.sum_le_sum, Finset.sum_le_sum_of_subset_of_nonneg, Finset.sum_neg_distrib, Fintype.card_coe, Fintype.card_sum, Function.iterate_succ_apply', Matrix.conjTranspose_apply, Matrix.inv_submatrix_equiv, Matrix.nonsing_inv_eq_ringInverse, Matrix.of_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.submatrix_apply, Nat.cast_nonneg, Nat.cast_sum, Nat.cast_zero, Nat.find, Nat.find_min, Nat.find_spec, Nat.le_zero, NeZero.pos, Real.exp_add, Real.exp_le_exp, Real.exp_le_one_iff, Real.exp_pos, Real.exp_sum, Real.norm_eq_abs, Real.sq_sqrt, abs_of_nonneg, add_le_add, add_left_inj, ite_false, ite_true, le_max_left, le_max_right, le_mul_of_one_le_right, le_total, lt_max_of_lt_left, max_eq_left, max_eq_right, min_le_left, min_le_right, mul_le_mul, mul_le_mul_of_nonneg_left, mul_le_mul_of_nonneg_right, mul_le_of_le_one_left, mul_nonneg, mul_one, mul_pow, neg_sub, norm_mul, norm_nonneg, norm_sub_le, norm_sum_le, nsmul_eq_mul, one_le_pow₀, one_pow, pow_le_pow_left₀, pow_le_pow_right₀, RBM.pow_mul_exp_neg_le, pow_nonneg, Or.resolve_left, smul_eq_mul, sq_le_sq₀, sq_nonneg, sub_add_cancel, sub_eq_zero, sub_ne_zero, sub_self, zero_add, Sum.inr.inj.
Current forms (`#check`): `Finset.prod_le_prod` is the `MulLeftMono` monoid version (one hypothesis `∀ i ∈ s, f i ≤ g i`); for `ℝ` with nonnegative factors the two-hypothesis version is `Finset.prod_le_prod₀`, used here. `if_neg` is deprecated (warning text: "Use `ite_eq_right` instead"); the file uses `simp only [hyx, ite_false, zero_add]`.

## (d) Open issues and paper-delta candidates
Open issues: none mathematical; nothing blocked; no REQ.
- `T2391a`: the second estimate of `(eq:Sigma-empty-sum-zero)` (`A:731`) is the unweighted `Σ_{b∖{b_1}} |Σ^{(∅)}| = O(λ² + |1-t|)`, cited from [RBSO1D Claim 4.30] (`A:734`). B3 is the weighted form `Σ_{δ_r=x} |Σ^{(∅)}| (max|δ_i-δ_j|+1)^Q ≤ C (g² + 1 - t)` for every `Q`, as the interface `SigSumZeroAbs` asks for `Q ≤ 2(d-1)`; the band twin `KLsumZero_weighted` is labelled new (`KLIndStepA.lean:934`) and is used in (G2), (G3) of `KLIndStepB.lean`. Proved here from B2 and the exponential slice sum.
- `T2391b`: the TeX proves neither estimate of `(eq:Sigma-empty-sum-zero)` (it cites [YY_25 L3.10], [RBSO1D L4.29, Claim 4.30], `A:734`). In the BA cactus the `g²` gain of B2 comes from one unequal short chord, or from two unequal `M`-edges of a node (`‖M_{xy}‖ ≤ A^{1/2} g e^{-c|x-y|}`: one `M`-edge gives only `g`); the band has one label per node and one off-diagonal edge suffices (`KLIndStepA.lean:889-891`).
- `T2391c`: the constants `G, c, C` are explicit, uniform in the family `(L, g ≤ Λ, E, m, t)`, and depend on `(d, n, Λ, κ)` (and `Q`); the paper writes `≺`, `O` (as `T2385c`). B2 holds for `2 ≤ n`, `t ≤ 1`, every `σ`; B3 and B4 need `3 ≤ n`, `t i < 1`.
- O1: `SigSumZeroAbs` has no range for `n` or `t` (`T2385b`); `baSig_sumZeroAbs` carries `3 ≤ n`, `t i < 1`, as `sigSumZeroAbs_band` and its consumers (`KLIndStepB.lean:299, 364`).
