Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 04:03:05 UTC 2026

Scripts (Python, no Lean): `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2105/{inst.py,inst2.py,flow.py,mc.py,scale.py}`.
Sources read at `c9a24cf`: RBM2D `Green/FlucIterHigh.lean` (970 lines, statements :738-:751), `Green/MinorGoodLe.lean` (474 lines, :243, :277, :319); merged `RBM3D/Green/FlucIterGain.lean:727` (`FlucGainUpTo'`), `RBM3D/Defs/Semicircle.lean:179` (`zt E t = E + (1-t) mE E`, same formula as RBM2D `spectralZ`, `SpectralWindow:34`).

### (i) Exponent table

| # | Quantity | Value | Constraint it must satisfy | Slack |
|---|---|---|---|---|
| 1 | Index type | `Idx d (sz.L n) (sz.W n) = Z_{WL}^d`, `N = (WL)^d` = 216 at (3,3,2) | enters only as a `Fintype`/`DecidableEq` type (FIH header "d = 2"); no exponent or cardinality occurs in either file | none; RBM2D `Z2 (W L)` (FIH:59, docstring) becomes `Zd d (W*L)`; no `d = 2` token occurs in code of either file (grep below) |
| 2 | Moment order `2p`, budgets `(M, K)` of `FlucGainUpTo'`/`MinorDiffGainUpTo'` | `p = 2`: `M = K = 4` for the consumer `integral_norm_flucAvg_pow_le_iter_budget` (T2096: `2p ≤ M`, `2p ≤ K`) | target 1 hands `(B, ρ, M, K)` through unchanged (same `(M,K)` in hypothesis and conclusion, FIH:751-:765) | no constraint in the target; consumer slack 0 at `M = K = 2p` |
| 3 | Row family `(2d+1) W^d` | `#A = 7 · 8 = 56` at d=3, W=2 (RBM2D `5 W² = 20`); row weights `S_ij`: `0.05` (same block), `0.0125` (neighbour), `c = W^{-d} = 1/8`, `∑_j S_ij = 1` | consumer only (T2096): `0 ≤ T ≤ c ≤ ρ²`, `2p ≤ #A`. `c·#A = 2d+1 = 7 > 1`: the uniform-weight mass bound is false (D192, DECISIONS §30) | `2p = 4 ≤ 56`: slack 52; `c = 1/8 ≤ ρ² = 1`: slack 7/8 |
| 4 | Uniform-weight uses in the two files | 0 | FIH/MGL contain no `UniformWeight`/`BoundedWeight`/weight at all (grep count 0 each); the weight enters only through T2096's `integral_norm_flucAvg_pow_le_iter_budget`, already `BoundedWeight` | not applicable |
| 5 | Envelope `‖Z^{(S)}_k‖ ≤ 2(η⁻¹+1)`, `η = (zt E t).im = (1-t) Im mE` | `E=0, t=0`: `η = 1`, bound 4 | `|E| < 2`, `t < 1` (⇒ `η > 0`); `norm_minorDiff_le`: `2^q` per `q`-fold difference; `norm_applyOps_le`: `2^q` per word | `t < 1` and `|E| < 2` are exactly the merged `bddMeas_flucDiag` hypotheses; no `0 ≤ t` needed (`zt_im` holds for all real t) |
| 6 | Gain-free witness of `MinorDiffGainUpTo'` | `(B, ρ, M, K) = (64, 1, 2, 2)` at `E=t=0` | `2^q·2^q·2(η⁻¹+1) ≤ B ρ^q` for `q ≤ M`: `[4, 16, 64] ≤ 64` | slack 0 at `q = 2` |
| 7 | MGL: `Ψ ≤ 1/4` | `Ψ = 1/8` in the instance | gives `‖G^{(S)}_{aa}‖ ≥ 1 - 2Ψ ≥ 1/2` (`‖m‖ = 1`), hence `‖(G_{aa})⁻¹‖ ≤ 2` | at `Ψ = 1/4` slack 0; implied by `8MΨ ≤ 1` when `M ≥ 1` |
| 8 | MGL: level budget `8 M Ψ ≤ 1` | `M = 1`, `Ψ = 1/8`: `8MΨ = 1` | invariant `Ψ_j = Ψ + 8jΨ²`, step `Ψ_j + 2Ψ_j² ≤ Ψ_{j+1}` needs `Ψ_j ≤ 2Ψ`, i.e. `8jΨ ≤ 1` for `j < M` | slack 0 at the instance (boundary); script grid in (ii) |
| 9 | MGL: threshold `Ψ ↦ 2Ψ` | `2Ψ = 1/4` | `Ψ + 8 \|S\| Ψ² ≤ 2Ψ` for `\|S\| ≤ M` (from `8MΨ ≤ 1`) | 0 at `\|S\| = M` |
| 10 | Flow statement `minorGoodLe_of_goodEvent_flow` | `z = zt E u`, `m = mE E`, `u` real, `\|E\| ≤ 2`, `(zt E u).im ≠ 0` | `(zt E u).im = (1-u) Im mE ≠ 0` ⇔ `u ≠ 1 ∧ \|E\| < 2` (so `\|E\| ≤ 2` is implied-tight, `= 2` is excluded by `hz`) | see §29 rows |
| 11 | DECISIONS §29 (1): time domain | statement is pointwise algebra at one `ω`; `seqHflow` is Hermitian for every real `u` (used in `RBM3D/Green/IBP.lean:285` with arbitrary `u`); `u` is constrained only by `hz` | `0 ≤ u` not needed: true for `u < 0` too (strictly more general than the paper's `0 ≤ s`); FIH: `t < 1` is the hypothesis `ht`, `u` independent of `t` (`bddMeas_flucDiag hE ht u`) | no boundary issue |
| 12 | §29 (2): case-(ii) boundary `1 - ilambda²/L²` | not used (no `ilambda`, no window) | n/a | n/a |
| 13 | §29 (3): `L^d ≤ W^K` | not used; only `3 ≤ L` (field `Sizes.three_le_L`) | n/a | n/a |
| 14 | §29 (4): `∀ n` vs `∀ᶠ n` | both targets are stated at one fixed slice `n` (RBM2D: no `∀ n`, no `∀ᶠ`); constants `2`, `8`, `1/4` contain no `W`, `L`, `ilambda`; no `∀ᶠ n` is needed and none is introduced | keep the `n`-fixed shape (do not add `∀ᶠ n`) | n/a |

Renames needed in the port (all dimension-free): `d : Sizes` → `sz : Sizes d`; `Idx (d.L n) (d.W n)` → `Idx d (sz.L n) (sz.W n)`; `spectralZ E t`, `spectralM E`, `norm_spectralM`, `spectralZ_im`, `spectralM_im_pos` → `zt E t`, `mE E`, `norm_mE`, `zt_im`, `mE_im_pos`; `Coord` → `CoordF` (R4); `BddMeas d X` → `BddMeas sz X`; `Sizes.seqP d` → `Sizes.seqP sz`.
Exact form S1-25 must prove (hypothesis of target 1, kept as hypothesis): `MinorDiffGainUpTo' sz n u z m B ρ M K := 0 ≤ B ∧ 0 ≤ ρ ∧ ∀ (ι : Type) [Fintype ι] k L, (∀ i, ((L i).map Prod.snd).Nodup) → (∀ i, ∀ x ∈ L i, x.2 ≠ k i) → (∀ i, (L i).length ≤ M) → Fintype.card ι ≤ K → ∫ ω, ∏ i, ‖applyOps sz n (L i) (minorDiff sz n (qList (L i)) (flucDiagSet sz n u z m (k i))) ω‖ ∂(Sizes.seqP sz) ≤ B ^ Fintype.card ι * ρ ^ ∑ i, numQ (L i)` (RBM2D FIH:738, renamed); conclusion `FlucGainUpTo' sz n u (zt E t) (mE E) B ρ M K` (merged FlucIterGain:727).

### (ii) One concrete nondegenerate instance (d = 3, L = 3, W = 2, ilambda = g = 1/2, N = 216, 27 blocks of 8 points)

Command `python3 inst.py` (target 1 hypotheses; consumer row weights):
```
N = 216  blocks L^d = 27  block size W^d = 8
MinorDiffGainUpTo'(B,rho,M,K)=(64,1,2,2) gain-free witness: crude(q)=[4.0, 16.0, 64.0] <= B rho^q: True
row of S: same block 0.05, neighbour block 0.0125; #A=56; sum T = 1.0
c = W^-d = 0.125; c*#A = 7.0  (> 1: the uniform-weight mass bound c*#A<=1 is false, D192);  c <= rho^2=1: True; 2p=4 <= #A: True
flow: |E|<=2 True | Im z_0 = 1.0 != 0 | 0<=Psi<=1/4: True | 8*M*Psi = 1.0 <= 1
```
Target 1 at `E = 0`, `t = 0` (`|E| < 2`, `t < 1`), any real `u`, `(B,ρ,M,K) = (64,1,2,2)`: every hypothesis holds (witness of `MinorDiffGainUpTo'` is the gain-free crude bound above, no local law; non-vacuous since `K = 2` slots and words up to length `M = 2`).

Target 2 at `ω = 0`, `E = 0`, `Ψ = 1/8`, `M = 1`. `ω = 0` gives `H_u = 0`, `G = -(z_u)⁻¹ 1`. Command `python3 inst2.py` (u > 0 instance) and `python3 flow.py` (u = 0 and random samples, level recursion):
```
u=1/16, omega=0: Im z = 0.9375  max|G-m|_max = 0.06666666666666665 = u/(1-u) = 0.06666666666666667 <= Psi: True
diag |G_aa|^-1 = 0.9375 <= 2 ; offdiag |G_ab| = 0.0 <= 2Psi= 0.25 ; 8*M*Psi = 1.0
omega=0,u=0: max|G-m 1| = 0.0  Im z = 1.0
Psi=1/8, M=1: Psi<=1/4: True  8*M*Psi = 1.0 <= 1: True  threshold 2Psi = 0.25
u=0.01, z=0.99j: realized Psi_omega: min 0.0533 median 0.0670 max 0.1010
good event holds with Psi=1/8 in 200/200 samples; conclusion (off,diag<=2Psi=1/4, inv<=2 at levels 0,1) verified on those
recursion/invariant grid: 6569 cases, violations: 0
```
So `GoodEvent (green (seqHflow sz n u ω) (zt 0 u)) (mE 0) (1/8)` holds at `ω = 0`, `u = 1/16` (`‖G - m‖_max = 1/15`) and at `u = 0` (exact), and the conclusion holds with `2Ψ = 1/4`, `M = 1`. Same file output, random samples at `u = 0.1` have `Ψ_ω ∈ [0.17, 0.31]` (earlier run, `u` edited to 0.01 afterwards), so `Ψ = 1/8` needs `u ≲ 0.02` at `W = 2`; a nondegenerate Lean instance is the deterministic `ω = 0, u = 1/16`.

External-hypothesis limit check (TEAM §8 lesson 14), for `MinorDiffGainUpTo'` at `q = 0`, one slot, `ρ`-free: `B_W := (E|Z_k|²)^{1/2}` for `E = 0`, `u = t = 1/2`, `g = 1/2`, `L = 3`, `d = 3`, `W = 2,3,4` (conditional expectation `E_k` by resampling row `k` against the exact minor `G^{(k)}`; 200 samples each; `python3 scale.py`):
```
W=2 N=216 samples=200  B_W=(E|Z|^2)^(1/2)=0.1899  B_W*W^(d/2)=0.5371
W=3 N=729 samples=200  B_W=(E|Z|^2)^(1/2)=0.1108  B_W*W^(d/2)=0.5757
W=4 N=1728 samples=200  B_W=(E|Z|^2)^(1/2)=0.0642  B_W*W^(d/2)=0.5138
log-slope W=2->4: -1.5640965471771138  (d/2 = 1.5)
```
So the hypothesis at `q = 0` has the scale `B ≈ 0.55 · W^{-d/2}` (d-dimensional exponent `d/2 = 3/2`; RBM2D's `d = 2` exponent would be 1), consistent with a satisfiable asymptotic form; the gain `ρ^q` for `q ≥ 1` (minor differences) is S1-25's content and is not checked here.

Numeric check (iii), `d = 3`, `L = 3`, `W = 2`, `g = 1/2`, `E = 0`, `u = t = 1/2` (`z = i/2`, `η = 1/2`), moment order 4 (`p = 2`), 10^4 samples, 48 inner resamples for each `E_k`, `T_j = S_{0j}` on `A = {j : block(j) - block(0) ∈ {0} ∪ nbrs}`, `python3 mc.py 1000 48` (1326 s):
```
|A|=56 (expected (2d+1)W^d=56); sum T=1.000000000000; max T=0.050000; W^-d=0.125
samples=10000 inner=48 time=1326s
MC E|sum_k T_k Z_k|^4 = 3.2556e-06 (se 7.5e-08)
MC max_k E|Z_k|^4 = 2.8655e-03  => B_mc = 0.2314;  B_mc^4 = 2.8655e-03; (triangle bound B^4 for the average)
MC mean |Z_k|^2 = 3.5609e-02; E|avg|^2 = 1.2513e-03
budget (2p+1)(2p)^2p (2^(2p-1) rho B)^2p, p=2, rho=sqrt(W^-d)=0.35355:
   B=B_mc   : 2.3475e+02
   B=crude 2(1/eta+1)=6.0: 1.0617e+08
MC <= budget(B_mc): True;  MC/B_mc^4 = 0.0011
2*(E|avg|^2)^2 = 3.1315033799999996e-06  vs MC E|avg|^4 = 3.2556e-06
```
Reading: the weighted average gains a factor `1/900` over the triangle bound `B^4` (`Σ T_k² ≈ 0.0275`; complex-Gaussian law `E|X|⁴ = 2(E|X|²)²` agrees within 4%); the budget of `integral_norm_flucAvg_pow_le_iter_budget` at `ρ = √c`, `B = B_mc` (2.3e2) and at the crude `B` (1.1e8) both dominate the Monte Carlo value; at `W = 2` the budget is not sharp (`ρ = 0.354`), only consistent. The inner `E_k` has Monte Carlo noise (48 resamples), so the number is a consistency check, not a tight value.

grep of `d = 2` tokens and weights in the two RBM2D sources (`grep -c "UniformWeight\|BoundedWeight\|uniformWeight" FIH.lean MGL.lean`; `grep -n "d = 2\|Z2\|zdist2\|W ^ 2\|W⁻²\|scaleM\|ellT\|ellStar"`, code lines only):
```
MGL.lean:0
FIH.lean:0
FIH.lean:59:Z2 (W L)` (its `Fintype` and `DecidableEq` structure): no exponent or cardinality of the index
```
(the portmap's `d=2:1` of FIH and MGL are the headings `## d = 2` at FIH:56, MGL:67, docstrings only).

### Verdict per target

- `flucGainUpTo'_of_minorDiffGainUpTo'` (FIH:751): **PASS**. Hypotheses `|E| < 2`, `t < 1`, `MinorDiffGainUpTo' … B ρ M K` hold at the instance (rows 5, 6); no dimension-specific exponent; unchanged at `d ≥ 3`; `MinorDiffGainUpTo'` stays a hypothesis (form above) for S1-25.
- `minorGoodLe_of_goodEvent_flow` (MGL:319) with `minorGoodLe_of_goodEvent`, `norm_gEnt_le_of_goodEvent`, `isUnit_det_Hflow_submatrix_sub`, `gEnt_insert_of_ne`: **PASS**. §29 (1)-(4): no `0 ≤ u`, `u < 1` (beyond `hz`), `ilambda`, `L^d ≤ W^K` or `∀ n`/`∀ᶠ n` is used; constants `1/4`, `8`, `2` are dimension-free (rows 7-9, 11-14); instance at `ω = 0`, `u = 1/16`, `Ψ = 1/8`, `M = 1`.
- All other public declarations of both files (word/minor algebra, `greenSetMat`, `gEnt`, `minorDiff`, `qList`, envelope lemmas): **PASS** as renamed; none uses a weight, `ℓ`, `M`-scale or `W^d` count, so the `d = 2 → d` exponent changes are limited to the type `Idx d …`.

## (b) Script output (stage 1b, rerun by rule H; branch held 1869adf at the start of this stage)

```
$ TZ=UTC git log -3 --format="%h %cd %s" --date=format-local:"%Y-%m-%d %H:%M:%S UTC"
f9b6449 2026-10-04 04:48:55 UTC T2105: header note on the equation numbering (4.x) of [YY_25]
1869adf 2026-10-04 04:26:11 UTC T2105: S1-22 Green/MinorGoodLe (port of RBM2D FlucIterHigh + MinorGoodLe)
e56d95c 2026-10-04 03:29:39 UTC T2103: merge ST2-28 Induction/LoopGenN + Induction/QVN (proves STLoopGenNForm, HierarchyN)
$ git diff --stat main...t/T2105   (main = 90a2761)
 RBM3D/Green/MinorGoodLe.lean | 1326 ++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean       |    2 +
 2 files changed, 1328 insertions(+)
$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/Green/MinorGoodLe.lean   (exit code of grep)
grep exit=1 (1 = no match)
$ wc -l RBM3D/Green/MinorGoodLe.lean
    1326 RBM3D/Green/MinorGoodLe.lean
```

Module build (command, tail of output, times from date -u: Sun Oct  4 04:47:50 to Sun Oct  4 04:48:09 UTC):
```
$ lake build RBM3D.Green.MinorGoodLe
✔ [3334/3334] Built RBM3D.Green.MinorGoodLe (13s)
Build completed successfully (3334 jobs).
exit=0
```
Full build (the root does not import the new module yet; the hub adds the import at merge), Sun Oct  4 04:48:23 to Sun Oct  4 04:48:27 UTC:
```
$ lake build
RBM3D.lean:150:0: axiom audit: 3256 theorems, 1184 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (3851 jobs).
exit=0
```

Registry pre-check (ST1-COMMON item 8; scratch file outside the repository: `import RBM3D`, `import RBM3D.Green.MinorGoodLe`, `#assert_rbm_axioms`), Sun Oct  4 04:48:27 to Sun Oct  4 04:48:51 UTC:
```
$ lake env lean precheck.lean | grep ...   (precheck.lean = the three lines above; registry diff lines cut at 250 characters)
axiom audit: 3320 theorems, 1197 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.Green.MinorDiffGainUpTo': 1 [no certificate]
  RBM.Green.FlucGainUpTo': 3 [no certificate]
premises found by scanning: 83 (borrowed 2, owed 65, structural 16).
registry: 5 borrowed + 102 owed + 39 structural; 63 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
exit=0
```
Registry lines added to `RBM3D/Test/Axioms.lean` (diff of the branch):
```
+   `RBM.Green.MinorDiffGainUpTo', -- the minor-difference gain for the iterated differences `applyOps L (Δ_{κ_1} ⋯ Δ_{κ_q} Z^{(·)}_k)` behind `(GavLGEX)` (`3_5:33`; Lemma 4.1 of `[YY_25]`): hypothesis of `flucGainUpTo'_of_minorDiffGainUpTo'` (T2105,
+   `RBM.Green.AgreeOffRows,   -- two samples agree on every coordinate off the rows in the finite set `S` (the `Finset` version of `AgreeOffRow`): hypothesis of `Xentry_congr_of_not_mem`, `Hflow_submatrix_set_congr` (T2105, S1-22)
```

Axioms (`lake env lean` on a scratch file with `#print axioms` of all 70 public declarations of the file: 59 ported + 11 instances), Sun Oct  4 04:48:14 UTC:
```
$ grep -o "depends on axioms: \[.*\]\|does not depend on any axioms" axioms_out | sort | uniq -c
  66 depends on axioms: [propext, Classical.choice, Quot.sound]
   1 depends on axioms: [propext]
   3 does not depend on any axioms
$ grep -n "flucGainUpTo\|minorGoodLe_of_goodEvent\|inst_\|applyOps_eq_applyOps_minorDiff\|length_qList" axioms_out   (the targets, the instances, the only non-uniform line)
'length_qList' [propext]
'applyOps_eq_applyOps_minorDiff' [std3]
'flucGainUpTo'_of_minorDiffGainUpTo'' [std3]
'minorGoodLe_of_goodEvent' [std3]
'minorGoodLe_of_goodEvent_flow' [std3]
'MinorGoodLeInst.inst_*' (11 declarations, one line each in axioms_out) [std3]
(std3 = propext, Classical.choice, Quot.sound)
```

Target statements (extracted from `RBM3D/Green/MinorGoodLe.lean` by script `extract.py`: text from the declaration keyword to `:=`):
```
-- line 764 (RBM2D FlucIterHigh.lean:751, c9a24cf); `MinorDiffGainUpTo'` defined at line 751 (RBM2D :738)
theorem flucGainUpTo'_of_minorDiffGainUpTo' (hE : |E| < 2) (ht : t < 1) (u : ℝ) {B ρ : ℝ}
    {M K : ℕ} (h : MinorDiffGainUpTo' sz n u (zt E t) (mE E) B ρ M K) :
    FlucGainUpTo' sz n u (zt E t) (mE E) B ρ M K

-- line 1019 (RBM2D MinorGoodLe.lean:319)
theorem minorGoodLe_of_goodEvent_flow {E : ℝ} (hE : |E| ≤ 2) (hz : (zt E u).im ≠ 0)
    (hΨ0 : 0 ≤ Ψ) (hΨ4 : Ψ ≤ 1 / 4) (hMΨ : 8 * M * Ψ ≤ 1)
    (hG : GoodEvent (green (Sizes.seqHflow sz n u ω) (zt E u)) (mE E) Ψ) :
    MinorGoodLe sz n u (zt E u) (mE E) ω (2 * Ψ) M

-- body of `MinorDiffGainUpTo'` (lines 751-762): identical to RBM2D :738 after renaming (block diff below); the form S1-25 proves is in (a)
```
Target 1 hands `(B, ρ, M, K)` through unchanged, so the exponent table of (a) row 2-3 applies as is; the `d`-dimensional exponents (`2d+1 = 7` rows of `W^d = 8` points, `#A = 56`, `d/2 = 3/2` in the scale of `B`) enter only through the consumer `integral_norm_flucAvg_pow_le_iter_budget` (T2096) and S1-25, not through any statement of this file.

Compiled nonempty instances (`d = 3`, `L = 3`, `W = 2`, `lam = 1/2`, `Idx = Z_6^3`; `szH : Sizes 3`):
```
example (u : ℝ) : FlucGainUpTo' szH 0 u (zt 0 0) (mE 0) 64 1 2 2 :=
  flucGainUpTo'_of_minorDiffGainUpTo' (E := 0) (t := 0) hE0 (by norm_num) u (minorDiffGain_szH u)

theorem inst_flucGain_word (u : ℝ) :
    ∫ ω, ∏ i : Fin 1, ‖applyOps szH 0 (slotWord i)
        (flucDiag szH 0 u (zt 0 0) (mE 0) (slotK i)) ω‖ ∂(Sizes.seqP szH)
      ≤ 64 ^ Fintype.card (Fin 1) * 1 ^ ∑ i : Fin 1, numQ (slotWord i)
  -- proved by `(flucGainUpTo'_of_minorDiffGainUpTo' ...).gain (Fin 1) slotK slotWord` with the Nodup, row-distinctness, length and cardinality side goals closed by `simp`/`decide`

theorem inst_minorGoodLe_flow :
    MinorGoodLe szH 0 (1 / 16) (zt 0 (1 / 16)) (mE 0) 0 (2 * (1 / 8)) 1 :=
  minorGoodLe_of_goodEvent_flow (E := 0) (by norm_num) zt_im_ne (by norm_num) (by norm_num)
    (by norm_num) goodEvent_omega_zero

```

Statement diff against RBM2D at `c9a24cf` (`xform.py` applies R1-R4 and `spectralZ/spectralM → zt/mE` to the two RBM2D files; `stmtdiff.py` compares every public declaration's statement text, comments stripped; `def`/`structure` bodies compared separately):
```
RBM2D public declarations (c9a24cf, after the renaming script): 59
identical statement text: 59
different: []
missing in RBM3D file: []
public in RBM3D file but not in RBM2D (new): ['inst_flucGain_word', 'inst_annihilation', 'inst_qList', 'inst_finDepOffRows', 'inst_minorGoodLe_flow', 'inst_minorGoodLe_general', 'inst_isUnit_det', 'inst_norm_gEnt', 'inst_gEnt_insert', 'inst_level_one', 'inst_gEnt_empty']
$ python3 (declaration-block diff, comments stripped, statement + proof, 91 RBM2D blocks vs the file)
MinorDiffGainUpTo', MinorGoodLe (all 5 fields), FinDepOffRows, AgreeOffRows, offRowsCoords, greenSetMat, gEnt, minorDiff, qList, greenSetDiagCentered, flucDiagSet, insertRowEquiv: body identical after renaming.
proof-level differences (statements unchanged): flucIterHigh_norm_green_zt_le (RBM2D norm_green_le -> norm_Gsig_le_inv_eta true + private flucIterHigh_Gres_true_eq_green), isUnit_det_Hflow_submatrix_sub (isUnit_sub_smul_one_of_im_ne_zero -> RBM.isUnit_sub_smul_of_isHermitian).
dropped: none of the 59 public declarations. RBM2D's 27 `private` check declarations (flucIterHigh_check_*, minorGoodLe_check_*, d = 2 sizes) are replaced by the 11 public d = 3 instances (`inst_*`) and the private instance helpers; the file has 34 `private` declarations in all (`grep -c "^private"`).
```

Name-clash check (every new public name against `main` = 90a2761, `git grep` for a declaration of the same short name):
```
$ git -C RBM3D --no-optional-locks grep -nE "^[[:space:]]*(private |protected )?(noncomputable )?(theorem|lemma|def|abbrev|structure|instance) ([A-Za-z.]*\.)?<short>([[:space:]]|$)" main -- RBM3D   (59 names, then the 11 inst_ names with theorem|def)
FinDepOffRows.comp        1
FinDepOffRows.sub        3
(hits for short names comp, sub are BddMeas.sub, FinDepOffRow.comp, FinDepOffRow.sub, Tame.sub: different full names; no declaration FinDepOffRows, AgreeOffRows, greenSetMat, MinorDiffGainUpTo', MinorGoodLe ... exists on main; the 11 inst_ names: 0 hits; the registry pre-check above compiled with all of RBM3D imported, so no full-name clash)
```

Port citation (RBM2D read-only, `git show c9a24cf:...`):
```
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h c9a24cf
c9a24cf
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Green/FlucIterHigh.lean RBM2D/Green/MinorGoodLe.lean
 RBM2D/Green/FlucIterHigh.lean | 279 +++++-------------------------------------
 RBM2D/Green/MinorGoodLe.lean  | 181 +++------------------------
 2 files changed, 44 insertions(+), 416 deletions(-)
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h   (HEAD)
9e0f275
sources: RBM2D/Green/FlucIterHigh.lean (970 lines at c9a24cf; :738 MinorDiffGainUpTo', :751 flucGainUpTo'_of_minorDiffGainUpTo'), RBM2D/Green/MinorGoodLe.lean (474 lines; :243 MinorGoodLe, :277 minorGoodLe_of_goodEvent, :319 minorGoodLe_of_goodEvent_flow)
```

d = 2 tokens and weights in the new file:
```
$ grep -c "d = 2\|Z2\|W \^ 2\|zdist2" RBM3D/Green/MinorGoodLe.lean; grep -n "UniformWeight\|BoundedWeight" RBM3D/Green/MinorGoodLe.lean
0
64:weight (`UniformWeight`/`BoundedWeight`), so DECISIONS §30 (D192) does not touch it: the weights
66:`BoundedWeight`.  `MinorGoodLe`'s statements are pointwise in `ω` and independent of `∀ᶠ n`,
$ grep -n "^import" RBM3D/Green/MinorGoodLe.lean
6:import RBM3D.Green.FlucIterGain
7:import Mathlib.Analysis.Matrix.MeasurableSpace
8:import Mathlib.Topology.Instances.Matrix
```

### Narrative
- At the start of this stage branch `t/T2105` held 1869adf (04:26:11 UTC) with the two sole writable files; the Lean text had no `sorry`. This stage re-ran the module build, the full build, the registry pre-check and the axioms, redid the statement diff against RBM2D `c9a24cf`, and added one docstring note (commit f9b6449): the equation numbers (4.1)-(4.3), (4.9) quoted in the file are those of `[YY_25]` (via RBM2D), not of arXiv:2507.20274.
- Target 1 `flucGainUpTo'_of_minorDiffGainUpTo'` (line 764) and target 2 `minorGoodLe_of_goodEvent_flow` (line 1019) have RBM2D's statements after renaming (59 of 59 public statements identical; the proofs of 2 declarations differ, listed above). No `d = 2` token and no weight (`UniformWeight`/`BoundedWeight`) occurs in code, so D192 is not touched; the weight enters only through T2096's consumer, which is already bounded-weight.
- `MinorDiffGainUpTo'` stays a hypothesis of target 1 in the form of RBM2D :738 (exact form in (a)); S1-25 proves it. Registry: `MinorDiffGainUpTo'` appended as owed, `AgreeOffRows` as structural; pre-check exit 0.
- Instance 1 (an `example`): `E = t = 0`, `(B, ρ, M, K) = (64, 1, 2, 2)`, hypotheses `|E| < 2`, `t < 1` and `MinorDiffGainUpTo'` all discharged, the last by the crude bound of `norm_minorDiff_le`/`norm_flucDiagSet_le_env`/`norm_applyOps_le` (tight at `q = 2`). `ρ = 1`, so it is gain-free: it shows the hypotheses are satisfiable and the theorem applies, not a gain. `inst_flucGain_word` applies the conclusion to one slot with a word `Q_{(0,0,1)} Q_{(0,1,0)}` of `numQ = 2 = M`.
- Instance 2 (`inst_minorGoodLe_flow`): sample point `ω = 0`, `u = 1/16`, `E = 0`, `Ψ = 1/8`, `M = 1`; `H_u = 0`, `G = (16/15) i · 1`, `‖G - m 1‖_max = 1/15 ≤ Ψ`, every hypothesis of target 2 proved (`8MΨ = 1` is the boundary of the level budget). `inst_gEnt_empty` gives the level-`∅` entry `G_aa = (16/15) i`, while `m = mE 0 = i`, so the conclusion is about a point where `G ≠ m 1`.
- DECISIONS §29 items for target 2 (as in (a) rows 11-14): the statement is pointwise algebra at one `ω`; no `0 ≤ u`, no `∀ᶠ n`, no `ilambda`, no `L^d ≤ W^K` appears in either target (`u` is only constrained by `hz`).
- The full build does not yet import the module (the hub adds the root import at merge); the registry pre-check imports it. `FlucGainUpTo'` (registered owed by T2096) is now concluded by target 1, so the scan lists it among the registered premises carrying nothing; its registry line is unchanged (append-only rule).

## (c) Verified names (`env.contains` by `lean` script at 04:46:36 UTC; all `true` = present)
Mathlib, used in the file: Real.sqrt_sq; Complex.norm_real; Complex.norm_I; Complex.I_ne_zero; inv_mul_cancel₀; inv_le_comm₀;
Matrix.inv_eq_right_inv; Matrix.inv_submatrix_equiv; Matrix.nonsing_inv_mul; Matrix.isUnit_iff_isUnit_det; Matrix.nonsing_inv_eq_ringInverse;
Ring.inverse_eq_inv'; List.not_mem_nil; List.mem_cons; Finset.card_insert_of_notMem; Finset.notMem_empty; Finset.prod_le_prod₀;
Finset.induction_on; MeasureTheory.integral_mono_of_nonneg (each one `present: true`, usage counted by `grep -c` in the file: >= 1).
RBM3D, used: RBM.isUnit_sub_smul_of_isHermitian; RBM.Gauss.norm_Gsig_le_inv_eta; RBM.Gauss.norm_matrix_entry_le_opNorm; RBM.green.
Verified absent in RBM3D (RBM2D names replaced in the port): RBM.Green.norm_green_le, RBM.norm_green_le, RBM.isUnit_sub_smul_one_of_im_ne_zero,
RBM.Gauss.isUnit_sub_smul_one_of_im_ne_zero, RBM.Ind.norm_apply_le_l2_opNorm, RBM.Gauss.Sizes.seqHflow_zero, RBM.Green.spectralZ, RBM.Gauss.spectralZ.

## (d) Open issues and paper-delta candidates
- Open for S1-25: prove `MinorDiffGainUpTo' sz n u (zt E t) (mE E) B ρ M K` (body at line 751) with `ρ < 1`; (a) checks only its `q = 0` scale numerically (`B ≈ 0.55 W^{-d/2}`, exponent `d/2 = 3/2`, not RBM2D's 1); the gain for `q ≥ 1` is not checked.
- Observation: RBM2D HEAD (9e0f275) differs from the pinned `c9a24cf` in both source files (diff-stat above); the port follows `c9a24cf` as the ticket pins.
- Observation: the registry line for `FlucGainUpTo'` (T2096) describes it as proved by S1-22; the dispatcher may mark or drop it.
- T2105a (Lean generalizes the paper): target 1 holds at every real `u` with `|E| < 2`, `t < 1`; target 2 at every real `u` with `(zt E u).im ≠ 0`, `|E| ≤ 2`; the paper's flow time is `0 ≤ s ≤ t < 1`. No loss.
- T2105b (paper does not state it): the paper has no higher-order minor expansion, no minors `G^{(S)}` and no level budget: `(GavLGEX)` (`3_5:33`) is deferred to Lemma 4.1 of `[YY_25]` (`3_5:37`). Lean adds `MinorDiffGainUpTo'` (hypothesis, owed by S1-25) and `MinorGoodLe` with the constants `2Ψ`, `8MΨ ≤ 1`, `‖(G^{(S)}_{aa})⁻¹‖ ≤ 2`, which are Lean choices (dimension-free).
- T2105c (numbering): the equation numbers (4.1)-(4.3), (4.9) in docstrings and in the registry line are `[YY_25]`'s, inherited from RBM2D; arXiv:2507.20274 has no such equations.
