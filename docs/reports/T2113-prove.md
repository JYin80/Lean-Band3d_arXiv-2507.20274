Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 05:41:16 UTC 2026

Sources read: RBM2D `Green/MinorDiff.lean` and `Green/MinorDiffCond.lean` at `c9a24cf` (1388 and 1464 lines; `:907` is `bddMeas_applyOps_minorDiff_flucDiagSet`), merged `RBM3D/Green/MinorGoodLe.lean` (`MinorGoodLe` :943, `MinorDiffGainUpTo'` :751), paper `3_5_Loop_Hierarchy.tex:14-33` (`lem_GbEXP`). Scripts (Python, no Lean): `scratchpad/T2113/{diff.py,ident.py,inst3.py}`, outputs `out_u05.txt`, `out_u002.txt`.

### (i) Exponent table

Mathematics of the file (all statements pointwise in one sample `ω`, one slice `n`): `Δ_κ Y^{(S)} = Y^{(S)} - Y^{(S∪κ)}`; `DiffBd Ψ I M n c p Y :⇔ ∀ l S, l.Nodup, l∩I=∅, |l| ≤ n, |S|+|l| ≤ M ⇒ ‖Δ_{l} Y^{(S)}‖ ≤ c Ψ^{p+|l|}` (the bound is `c·Ψ^{p+|l|}` with `c` independent of `Ψ`, not `(cΨ)^{|l|}`). Top estimate (`MinorDiff:792`): `‖Δ_{κ_1}⋯Δ_{κ_m}(G^{(·)}_{kk}-m)‖ ≤ C_{m-1} Ψ^{m+1}`, `C_{m-1} = minorDiffC (m-1)`.

| # | Quantity | Value | Constraint | Slack |
|---|---|---|---|---|
| 1 | `d = 2` tokens in code of `MinorDiff` at `c9a24cf` | 0 (`grep` of `d = 2|Z2|zdist2|W ^ 2|W⁻²|scaleM|ellT|ellStar|Meta|ellz|tailT|UniformWeight|BoundedWeight|size|1/5` hits only the docstring heading `## d = 2` :76 and the word "size" in prose) | portmap `d=2:1` is that heading | the file depends on `d` only through the index type `Idx (d.L n) (d.W n)` → `Idx d (sz.L n) (sz.W n)` (R1, R2); no exponent, no weight, no `W^2`: nothing to recompute |
| 2 | `atomC 0 = 2`, `atomC (r+1) = 16^r atomC r^5` | `2, 32, 2^29 = 536870912` | `2 ≤ atomC r` (induction `2^5 ≤ atomC^5`, `16^r ≥ 1`) | dimension-free (RBM1D constants, not the paper's) |
| 3 | `minorDiffC n = 4^n atomC n^3` | `8, 131072, 2^91 ≈ 2.476e27` (n = 0,1,2) | `1 ≤ minorDiffC`, monotone in `n` | dimension-free; `C_3 = 2^91` makes the `m = 3` bound vacuous for `Ψ` of the size of the data (table row 11) |
| 4 | `DiffBd.mul` constant | `2^n c₁c₂`, orders add `p+q` | `0 ≤ Ψ`, `0 ≤ c₁,c₂`; `n`-fold Leibniz = `2^n` terms | none |
| 5 | `DiffBd.delta`/`.shift`/`.congr` budgets | `(M+1,n+1) → (M,n)`; shift `(M+1) → M`; `congr` needs agreement on `|U| ≤ M` | one unit of level budget per `Δ_κ` or shift; invariant `B+|T| ≤ M` in `diffBd_atom` | exact (0), as in RBM2D |
| 6 | `diffBd_atom` orders | `gFam a≠b`: `p = 1`; `gInvFam`: `p = 0`; constant `atomC r` | `0 ≤ Ψ ≤ 1` (for `mono_p`), `MinorGoodLe … Ψ M` | `Ψ ≤ 1` is implied by `Ψ = 2Ψ₀`, `8MΨ₀ ≤ 1` (`Ψ ≤ 1/(4M)`), `M ≥ 1` |
| 7 | Hypotheses of `norm_minorDiff_greenSetDiagCentered_le` | `k≠κ`, `(κ::l).Nodup`, `∀x∈l, x≠k`, `|l|+1 ≤ M`, `0≤Ψ≤1` | all deterministic; `MinorGoodLe` from `minorGoodLe_of_goodEvent_flow` (needs `|E| ≤ 2`, `Im z ≠ 0`, `Ψ₀ ≤ 1/4`, `8MΨ₀ ≤ 1`) | `M = 3`: `Ψ₀ ≤ 1/24` |
| 8 | Endpoint `bddMeas_applyOps_minorDiff_flucDiagSet` | hypotheses `|E| < 2`, `t < 1`, `u : ℝ`, any `k`, any word `L` | no `Nodup`, no `Ψ`, no `0 ≤ u` (unlike the paper's `0 ≤ s`): true for all real `u` (D210) | none; boundedness and measurability only (`BddMeas`) |
| 9 | DECISIONS §29 (1) `0 ≤ s`, `t < 1` | `t < 1` and `|E| < 2` hypotheses of `bddMeas_flucDiagSet`; `u` free | pointwise algebra | no boundary issue |
| 10 | §29 (2)(3)(4): `1 - ilambda²/L²`, `L^d ≤ W^K`, `∀ n` vs `∀ᶠ n` | not used; no `ilambda`, no window, no `W` or `L` in any constant; fixed slice `n` (RBM2D has no `∀ n`, no `∀ᶠ`) | keep the fixed-slice shape | n/a |
| 11 | Per-layer gain, `d`-dimensional | one power of `Ψ` per `Δ_κ`; `Ψ ≥ W^{-d/2}` (paper `3_5:27`, D213), so the per-layer scale is `W^{-d/2}` (RBM2D `W^{-1}`) | measured exponents of `rms|Δ^m|` (script (iii)): `m = 1,2,3` ≈ `3, 4.5, 6 = (m+1)d/2` at `d = 3`; per-layer step `≈ 1.5 = d/2` | see (iii) |
| 12 | Gain interface `MinorDiffGainUpTo' sz n u (zt E t) (mE E) B ρ M K` | discharged by **S1-26**, not S1-25: RBM2D `MinorDiffCond.lean:869` `minorDiffGainUpTo'_goodEvent` with `B = 2(2 minorDiffC M·Ψ + condCost)`, `ρ = 2Ψ`, `Ψ = 2δ(n)` (`:869-895`); S1-25 supplies the deterministic word estimate `norm_minorDiff_greenSetDiagCentered_le` and `bddMeas_…` that `MinorDiffCond:360, :413` consume | `ρ = 4δ < 1` needs `δ < 1/4` (implied by `8Mδ ≤ 1`, `M ≥ 1`: `ρ ≤ 1/(2M) ≤ 1/2`); `B ≍ Ψ` | for `q ≥ 1`: `B ρ^q ≈ Ψ^{q+1}`, per layer `ρ = 2Ψ ≥ W^{-d/2}`; for `q = 0`: `B ≈ 0.55 W^{-d/2}` (T2105 report). `d` enters S1-26 only through the row count `size n = (W L)^d` of `meas_badTower_le` (RBM2D `(W L)²`), not S1-25 |
| 13 | Declarations dropped | none: all 50 public declarations before the private `Checks` section (:915-1283) are ported; the `Checks` section and the `#print axioms` tail are replaced by this ticket's own instances | portmap row 55 marks nothing unused | — |

### (ii) One concrete nondegenerate instance (`d = 3`, `L = 3`, `W = 2`, `N = 216`, `g = 1/2`, `E = 0`, `t = 1/2`)

`Sizes d` carries `3 ≤ L` only; every deterministic hypothesis of the targets is met at `ω = 0` (`H_u = 0`, `G = -z⁻¹·1`), `u = 1/32` (any real `u` is admitted), `z = zt 0 u = (1-u) i`, `m = i`, `M = 3`, rows `k = 0`, `κ = (1, 6, 7)` (three distinct rows, same block as `k`), `Ψ₀ = u/(1-u) = 1/31`, `Ψ = 2Ψ₀ = 2/31`. `python3 inst3.py`:
```
N = 216  |E|<2: True  t<1: True  Im z = 0.96875  u real, no 0<=u needed
GoodEvent Psi0 = max|G-m 1| = 0.032258064516129004 = u/(1-u) = 0.03225806451612903  Psi0<=1/4: True  8*M*Psi0 = 0.7741935483870961 <=1: True
MinorGoodLe threshold Psi = 2*Psi0 = 0.06451612903225801  0<=Psi<=1: True
rows k,kappa distinct: [0, 1, 6, 7]  (kappa::l).Nodup, l.length+1 =3 <= M =3
min |G_aa|^-1 = 0.96875 <=2; offdiag max = 0.0
m=1: |Delta^m (G_kk-m)| = 0.000e+00 <= C_1*Psi^2 = 3.330e-02: True
m=2: |Delta^m (G_kk-m)| = 0.000e+00 <= C_2*Psi^3 = 3.520e+01: True
m=3: |Delta^m (G_kk-m)| = 0.000e+00 <= C_3*Psi^4 = 4.289e+22: True
```
At `ω = 0` the matrix is diagonal, so the `Δ` are `0`: the hypotheses are nonempty (nonzero `Ψ`, three distinct rows, `M = 3`) but the bounds are trivial; the families are not constant (`G^{(S)}_{aa}` is `m/(1-u)` for `a ∉ S`, `0` for `a ∈ S`). Nontrivial `Δ` are checked on random samples below. Target 8 (`bddMeas_…`): `|E| = 0 < 2`, `t = 1/2 < 1`, `u = 1/32`, `k = 0`, `L = [(true,1),(false,6),(true,7)]`: no further hypothesis.

Exact identities behind `deltaFam_gFam_apply`, `deltaFam_gInvFam_apply`, `deltaFam_mul` on a random sample (`d = 3`, `W = 2`, `u = 1/2`, `python3 ident.py`):
```
Schur minor vs direct inverse, max err: 3.5333894300643197e-16
(4.9) |lhs-rhs| = 6.938893903907228e-18  |lhs| = 0.04071649351114049
reciprocal |lhs-rhs| = 8.369507079928947e-17  |lhs| = 0.06744281770168326
Leibniz |lhs-rhs| = 2.8609792490763984e-17
atomC 0,1,2 = [2.0, 32.0, 536870912.0]  minorDiffC 0,1,2 = [8.0, 131072.0, 2.4758800785707605e+27]
```

**(iii) Numeric check** (model of T2105 `scale.py`: `H = √u X`, variance `svarF`, `z = E + (1-u)i`, `t = u`; `Δ_{κ_1}⋯Δ_{κ_m}` computed as the signed sum over subsets of exact Schur minors; `Ψ_ω = max(max_{a≠b}|G_ab|, max_a|G_aa - m|)`; `W = 2, 3, 4`; 1000, 1000, 120 samples; rows `κ` in the block of `k` ("same") or in three neighbouring blocks ("near")). `python3 diff.py 0.5 1000 1000 120` (ticket data `u = 1/2`), tail, family `diag` = `G_kk - m`, rms over samples:
```
W=2 N=216 samples=1000 Psi_omega: min 0.4321 med 0.4946 max 0.6946; frac(8*3*Psi<=1)=0.000
W=4 N=1728 samples=120 Psi_omega: min 0.2078 med 0.2300 max 0.2712; frac(8*3*Psi<=1)=0.000
  diag m=1: rms W=2 4.259e-02 W=3 1.143e-02 W=4 5.908e-03  exponent W2->4 = 2.85
  diag m=2: rms W=2 9.875e-03 W=3 1.539e-03 W=4 4.609e-04  exponent W2->4 = 4.42
  diag m=3: rms W=2 3.305e-03 W=3 2.716e-04 W=4 6.882e-05  exponent W2->4 = 5.59
  diag: per-layer W-exponent of rms ratio (m=1->2, 2->3) between W=2 and W=4:  1.57, 1.16   (d/2 = 1.5)
  off: per-layer ... 1.51, 1.26 ; inv: ... 1.55, 1.18   (same block);  near block: diag 1.43, 1.52; off 1.43, 1.68; inv 1.33, 1.43
--- all samples (hypotheses not required): max |Delta^m diag same| / Psi_omega^{m+1}
  W=2: 0.913 0.418 0.367 | W=3: 0.453 0.212 0.151 | W=4: 0.421 0.132 0.116
```
At the ticket's data `u = 1/2`, `W = 2` the realized `Ψ_ω ∈ [0.43, 0.69]` for all samples, so `Ψ₀ ≤ 1/8` (`8MΨ₀ ≤ 1`, `M ≥ 1`) never holds: the hypotheses of `MinorGoodLe` do not hold on a random sample at these data, and the DiffBd statement is not claimed there (the ratios above only show the form `|Δ^m| ≲ Ψ_ω^{m+1}`). Instance with the hypotheses holding on random samples, `python3 diff.py 0.002 1000 1000 120`:
```
W=2 N=216 samples=1000 Psi_omega: min 0.0242 med 0.0301 max 0.0452; frac(8*3*Psi<=1)=0.993
W=3 N=729 samples=1000 Psi_omega: min 0.0151 med 0.0183 max 0.0262; frac(8*3*Psi<=1)=1.000
W=4 N=1728 samples=120 Psi_omega: min 0.0109 med 0.0129 max 0.0166; frac(8*3*Psi<=1)=1.000
  diag m=1: rms W=2 1.483e-04 W=3 3.971e-05 W=4 1.977e-05  exponent W2->4 = 2.91
  diag m=2: rms W=2 1.408e-06 W=3 2.201e-07 W=4 7.219e-08  exponent W2->4 = 4.29
  diag m=3: rms W=2 2.463e-08 W=3 2.125e-09 W=4 3.792e-10  exponent W2->4 = 6.02
  diag: per-layer W-exponent of rms ratio (m=1->2, 2->3) between W=2 and W=4:  1.38, 1.74   (d/2 = 1.5)
  W=2 same: #samples with 24 Psi<=1: 993; max ratios m=1,2,3: 0.248 0.064 0.0208  vs C_m = 8 1.31e+05 2.48e+27
  W=3 same: #samples with 24 Psi<=1: 1000; max ratios m=1,2,3: 0.138 0.0256 0.0104  vs C_m = 8 1.31e+05 2.48e+27
  W=4 same: #samples with 24 Psi<=1: 120; max ratios m=1,2,3: 0.112 0.0196 0.00742  vs C_m = 8 1.31e+05 2.48e+27
```
(ratio = `max |Δ^m(G_kk - m)| / (2Ψ_ω)^{m+1}` over the samples with `24Ψ_ω ≤ 1`, the hypotheses of `minorGoodLe_of_goodEvent_flow` at `M = 3` with `Ψ = 2Ψ_ω`; the near-block ratios are smaller still.) The ratios stay below `C_m` by factors `≥ 32`, `2·10⁶`, `10²⁹`: the bound is consistent with the data and very slack for `m ≥ 2`. The per-layer exponent of `W` is `d/2 = 1.5` within sampling error (range 1.16 to 1.74 over families and rows at 120 samples for `W = 4`); `|Δ^m| ∝ W^{-(m+1)d/2}`, i.e. `Ψ^{m+1}` at `Ψ ≍ W^{-d/2}`, so the layers `q ≥ 1` have `ρ ≍ W^{-d/2}` (RBM2D `W^{-1}`), consistent with the floor `W^{-d/2} ≤ Ψ` (D213).

External hypothesis `MinorDiffGainUpTo'` (stays a hypothesis here; discharged in S1-26): limit computation above gives `B ≈ 0.55 W^{-d/2}` at `q = 0` (T2105) and `|Δ^q (G_kk - m)| ∝ W^{-(q+1)d/2}` for `q = 1, 2, 3` at `d = 3` (rows `m = 1,2,3`), so `B ρ^q` with `B, ρ ≍ W^{-d/2}` is satisfiable with `ρ < 1`.

### Verdict per target

- `deltaFam`, `shiftFam`, `iterDeltaFam`, the calculus lemmas, `DiffBd` and `.le_self/.mono_*/.congr/.delta/.shift/.neg/.mul`, `minorDiff_eq_iterDeltaFam`, `gFam`, `gInvFam`, `deltaFam_gFam_apply`, `deltaFam_gInvFam_apply`, `atomC`, `minorDiffC`, `diffBd_atom`, `norm_minorDiff_greenSetDiagCentered_le`, `norm_greenSetDiagCentered_le`: **PASS**. Dimension-free; hypotheses nonempty at the instance (rows 2-7); the `d`-dimensional exponent enters only through `Ψ ≥ W^{-d/2}`, a hypothesis of other files.
- `minorDiff_qRow`, `minorDiff_flucDiagSet_eq`, `qList_nodup`, `mem_qList_ne`, `bddMeas_minorDiff`, `bddMeas_applyOps_minorDiff_flucDiagSet` (:907): **PASS**; hypotheses `|E| < 2`, `t < 1`, real `u` (row 8).
- Gain interface: **PASS** (nothing owed by S1-25; S1-26 discharges `MinorDiffGainUpTo'`, row 12). Note for the ticket: at `u = 1/2`, `W = 2` the `MinorGoodLe` hypotheses fail on random samples, so a Lean instance with nonzero `Δ` needs small `u` or a deterministic `ω`; the Lean instance at `ω = 0` is admissible and nonempty (hypotheses all hold, `Δ = 0`).

## (a′) Preflight corrections — Sun Oct  4 05:55:10 UTC 2026

Row 13 of (a) counts "50 public declarations" before the private `Checks` section; the script count is 58 (the `#print axioms` tail of RBM2D `c9a24cf:1285-1342` lists the same 58 names; `comm -3` of the two sorted name lists is empty, command in (b.6)). All 58 are ported, none dropped; no verdict changes. The Lean instance (b.4) uses `u = 1/31` (`Ψ₀ = 1/30`, `8·3·Ψ₀ = 4/5 ≤ 1`) instead of (a)'s `u = 1/32`, and five lattice sites `A..E` instead of rows `(1,6,7)`; same shape (three distinct rows `κ`, `M = 3`, `ω = 0`).

## (b) Script output — Sun Oct  4 05:55:10 UTC 2026 (stage 1b, `prover-hard`, Sonnet; branch `t/T2113`, commit 2479590)

### (b.1) Build
```
$ lake build RBM3D.Green.MinorDiff   (cwd /Users/junyin/Lean_proof/RBM3D-wt/T2113)
Build completed successfully (3335 jobs).
$ lake build   (full library; the root import of the new module is added by the hub at merge)
Build completed successfully (3856 jobs).
$ git diff --name-only main...t/T2113
RBM3D/Green/MinorDiff.lean
$ grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Green/MinorDiff.lean
0
$ wc -l RBM3D/Green/MinorDiff.lean
    1371
```

### (b.2) Axioms (`#print axioms` of all 93 public declarations of the file: 58 ported, 35 `MinorDiffInst.inst_*`)
```
$ lake env lean axioms.lean   (scratch file: import RBM3D.Green.MinorDiff, one #print axioms per public name, names extracted by script)
$ sed "s/.*depends on axioms: //" axioms.out | sort | uniq -c
  91 [propext, Classical.choice, Quot.sound]
   1 [propext, Quot.sound]
   1 [propext]
'DiffBd.mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'deltaFam_gFam_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'diffBd_atom' depends on axioms: [propext, Classical.choice, Quot.sound]
'norm_minorDiff_greenSetDiagCentered_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'norm_greenSetDiagCentered_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'bddMeas_applyOps_minorDiff_flucDiagSet' depends on axioms: [propext, Classical.choice, Quot.sound]
'MinorDiffInst.inst_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'MinorDiffInst.inst_bddMeas' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -E "mem_qList_ne|qList_nodup" axioms.out   (the two with fewer axioms)
'qList_nodup' depends on axioms: [propext]
'mem_qList_ne' depends on axioms: [propext, Quot.sound]
```

### (b.3) Key target statements, extracted by script (`extract.py`: declaration line to `:=`; line numbers of `RBM3D/Green/MinorDiff.lean`; the other 51 statements are covered by the diff of b.6)
```
905: theorem bddMeas_applyOps_minorDiff_flucDiagSet (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    (k : Idx d (sz.L n) (sz.W n)) (L : List (Bool × Idx d (sz.L n) (sz.W n))) :
    BddMeas sz (applyOps sz n L
      (minorDiff sz n (qList L) (flucDiagSet sz n u (zt E t) (mE E) k)))
790: theorem norm_minorDiff_greenSetDiagCentered_le (hg : MinorGoodLe sz n u z m ω Ψ M) (hΨ0 : 0 ≤ Ψ)
    (hΨ1 : Ψ ≤ 1) (k κ : Idx d (sz.L n) (sz.W n)) (l : List (Idx d (sz.L n) (sz.W n))) (hkκ : k ≠ κ)
    (hnd : (κ :: l).Nodup) (hkl : ∀ x ∈ l, x ≠ k) (hM : l.length + 1 ≤ M) :
    ‖minorDiff sz n (κ :: l) (greenSetDiagCentered sz n u z m k) ω‖
      ≤ minorDiffC l.length * Ψ ^ (l.length + 2)
834: theorem norm_greenSetDiagCentered_le (hg : MinorGoodLe sz n u z m ω Ψ M) (hΨ0 : 0 ≤ Ψ)
    (k : Idx d (sz.L n) (sz.W n)) (S : Finset (Idx d (sz.L n) (sz.W n))) (hS : S.card ≤ M) :
    ‖greenSetDiagCentered sz n u z m k S ω‖ ≤ Ψ
570: theorem diffBd_atom (hg : MinorGoodLe sz n u z m ω Ψ M) (hΨ0 : 0 ≤ Ψ) (hΨ1 : Ψ ≤ 1) :
    ∀ (r : ℕ) (I T : Finset (Idx d (sz.L n) (sz.W n))) (B : ℕ), B + T.card ≤ M →
      (∀ a b : Idx d (sz.L n) (sz.W n), a ∈ I → b ∈ I → a ≠ b →
        DiffBd Ψ I B r (atomC r) 1 (gFam sz n u z ω a b T))
      ∧ (∀ a : Idx d (sz.L n) (sz.W n), a ∈ I →
        DiffBd Ψ I B r (atomC r) 0 (gInvFam sz n u z ω a T))
224: def DiffBd (Ψ : ℝ) (I : Finset α) (M n : ℕ) (c : ℝ) (p : ℕ) (Y : Finset α → ℂ) : Prop
450: theorem deltaFam_gFam_apply (hg : MinorGoodLe sz n u z m ω Ψ M) (a b κ : Idx d (sz.L n) (sz.W n))
    (T S : Finset (Idx d (sz.L n) (sz.W n))) (hcard : (insert κ (S ∪ T)).card ≤ M) :
    deltaFam κ (gFam sz n u z ω a b T) S
      = gFam sz n u z ω a κ T S * gFam sz n u z ω κ b T S * gInvFam sz n u z ω κ T S
407: theorem minorDiff_eq_iterDeltaFam (l : List (Idx d (sz.L n) (sz.W n)))
    (Y : Finset (Idx d (sz.L n) (sz.W n)) → Sizes.SeqΩ sz → ℂ) (ω : Sizes.SeqΩ sz) :
    minorDiff sz n l Y ω = iterDeltaFam l (fun S => Y S ω) ∅
```

### (b.4) Compiled nonempty instances (`MinorDiffInst`, `d = 3`, `L = 3`, `W = 2`, `N = 216`, `E = 0`, `u = t = 1/31`, `ω = 0`, `M = 3`; all hypotheses proved)
```
$ grep -o "^theorem inst_[A-Za-z_]*" RBM3D/Green/MinorDiff.lean | sed s/theorem.inst_// | tr "
" " "
gEnt_nonconst constants endpoint endpoint_num diag diag_removed atom atom_entry atom_inv gFam gInvFam first_diff eq_iter bddMeas qList qList_nodup 
mem_qList_ne bddMeas_minorDiff qRow flucDiagSet_eq mul mul_use inv leibniz calculus monotone congr le_self zero mono neg congrBd delta mono_p shift 
private theorem check_hg :
    MinorGoodLe szM 0 (1 / 31) (zt 0 (1 / 31)) (mE 0) 0 (2 * (1 / 30)) 3 :=
  minorGoodLe_of_goodEvent_flow (E := 0) (by norm_num) zt_im_ne (by norm_num) (by norm_num)
    (by norm_num) goodEvent_omega_zero

theorem inst_endpoint :
    ‖minorDiff szM 0 [siteB, siteC, siteD]
        (greenSetDiagCentered szM 0 (1 / 31) (zt 0 (1 / 31)) (mE 0) siteA) 0‖
      ≤ minorDiffC [siteC, siteD].length * (2 * (1 / 30)) ^ ([siteC, siteD].length + 2) :=
  norm_minorDiff_greenSetDiagCentered_le check_hg (by norm_num) (by norm_num)
    siteA siteB [siteC, siteD] hAB (by simp [hBC, hBD, hCD]) (by simp [hCA, hDA]) (by decide)

theorem inst_bddMeas :
    BddMeas szM (applyOps szM 0 word3
      (minorDiff szM 0 (qList word3)
        (flucDiagSet szM 0 (1 / 31) (zt 0 (1 / 31)) (mE 0) siteA))) :=
  bddMeas_applyOps_minorDiff_flucDiagSet (E := 0) (t := 1 / 31) hE0 (by norm_num) (1 / 31)
    siteA word3

```

### (b.5) Name-clash grep (new public names against `main` = 6f8ca5b)
```
$ git grep -nE "^(@\[[a-z]+\] )?(private )?(noncomputable )?(protected )?(theorem|lemma|def|abbrev|structure|instance) (<the 47 top-level new names>)( |$)" main -- RBM3D | grep -v Green/MinorDiff.lean
       0
$ git grep -nE "namespace (DiffBd|MinorDiffInst)|DiffBd" main -- RBM3D | wc -l   (the namespaces DiffBd.* and MinorDiffInst.* are new)
       0
$ lake env lean precheck.lean   (below, b.7): a clash would be an "already declared" error; none
```

### (b.6) Port: source, renaming, statement diff
```
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks log -1 --format=%h ; (port commit named by the ticket: c9a24cf)
9e0f275
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks show c9a24cf:RBM2D/Green/MinorDiff.lean | wc -l
    1388
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Green/MinorDiff.lean | tail -2
 RBM2D/Green/MinorDiff.lean | 563 +++------------------------------------------
 1 file changed, 36 insertions(+), 527 deletions(-)
# ported text: RBM2D MinorDiff.lean:98-913 (calculus ... assembly); not ported: header :1-97 (rewritten), Checks :915-1283 and #print tail :1285-1388 (replaced by b.4)
# renaming script port.py (R1, R2, zt/mE; R3, R4 do not occur in this file):
body='\n'.join(lines[97:913])
b=body
b=b.replace('Idx (d.L n) (d.W n)','Idx d (sz.L n) (sz.W n)')
b=b.replace('Sizes.SeqΩ d','Sizes.SeqΩ sz')
b=b.replace('variable {d : Sizes} {n : ℕ}','variable {d : ℕ} {sz : Sizes d} {n : ℕ}')
for f in ['minorDiff','gEnt','gFam','gInvFam','MinorGoodLe','greenSetDiagCentered','flucDiagSet','qRow','applyOps','BddMeas']:
    b=re.sub(r'\b'+f+r' d\b',f+' sz',b)
b=b.replace('(d : Sizes) (n : ℕ)','(sz : Sizes d) (n : ℕ)')
b=b.replace('spectralZ E t','zt E t').replace('spectralM E','mE E')
b=b.replace('gEnt d n','gEnt sz n')
open(sys.argv[2],'w').write(b)
$ python3 port.py MinorDiff2D.lean body.lean ; sed s/greenSetMat d n/greenSetMat sz n/ ; diff body.lean <(file body from "### The difference calculus" to "### Compiled nonempty instances")
diff exit: 0   (0: the ported body is the renamed RBM2D text, no other change)
$ comm -3 <(sed -n 1285,1342p MinorDiff2D.lean | sed "s/#print axioms //" | sort) <(grep -v "^MinorDiffInst\." names.txt | sort) | wc -l
       0
$ grep -nE "d = 2|Z2|zdist2|W \^ 2|W⁻²|scaleM|ellT|ellStar|Meta|ellz|tailT|UniformWeight|BoundedWeight|1/5|inv2|L2|N2|W2" (RBM2D file | RBM3D file)
RBM2D:76:## d = 2 and differences from RBM1D
RBM3D:66:with `DecidableEq`): there is no `W`, `L`, `size`, no weight (`UniformWeight`/`BoundedWeight`, so
```

### (b.7) Registry pre-check (ST1-COMMON item 8; scratch file outside the repository)
```
$ cat scratchpad/T2113/precheck.lean
import RBM3D
import RBM3D.Green.MinorDiff

#assert_rbm_axioms
$ lake env lean scratchpad/T2113/precheck.lean ; echo $?
exit code: 0
axiom audit: 3457 theorems, 1228 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
  RBM.Green.MinorDiffGainUpTo': 1 [no certificate]
  RBM.Green.FlucGainUpTo': 3 [no certificate]
 RBM.Green.FlucGainUpTo',
lines containing "error": 0
```

### (b.8) Narrative
- **Scope.** One new file, `RBM3D/Green/MinorDiff.lean` (commit above); `Test/Axioms.lean` is not touched (no registry line needed, see below). The ported body (RBM2D `MinorDiff.lean:98-913`, 58 public declarations, none dropped) is the renamed RBM2D text; the `diff` of b.6 exits 0, so no statement and no proof line changed beyond R1/R2 and `zt`/`mE`. No hypothesis was added or weakened, no pinned signature changed.
- **`d = 2` tokens** (portmap `d=2:1`, ST1-COMMON item 2): the only hit of the token grep (b.6) in the RBM2D file is the docstring heading `## d = 2` (`:76`); the code depends on `d` only through the index type. Nothing to replace: no `W`, `L`, `size`, `lam`, weight, `ilambda`, `∀ᶠ` in any statement. `lam` occurs once, as data of the instance size sequence (`MinorDiff.lean:939`). Hence no statement here is false at `d ≥ 3`, and the exponent table of (a) (rows 1, 10) is confirmed by the build at `d = 3`.
- **DECISIONS §29 / §30.** `bddMeas_applyOps_minorDiff_flucDiagSet` and `minorDiff_flucDiagSet_eq` take `|E| < 2`, `t < 1` and a real `u` (no `0 ≤ u`, D210); the other statements are pointwise in `ω` with `MinorGoodLe` as hypothesis. No weight appears (§30 does not apply); the fixed slice `n` has no `∀ n`/`∀ᶠ`.
- **Gain interface.** `MinorDiffGainUpTo'` is discharged by **S1-26**, not by this file: RBM2D `MinorDiffCond.lean:869` (`minorDiffGainUpTo'_goodEvent`) concludes it with `B = 2 (2 · minorDiffC M · (2δ n) + condCost …)` and `ρ = 2 (2δ n)`, and consumes this file's `norm_minorDiff_greenSetDiagCentered_le` (`MinorDiffCond:390`) and `bddMeas_applyOps_minorDiff_flucDiagSet` (`MinorDiffCond:668`) (lines read from the `c9a24cf` blob). The estimate proved here has one factor `Ψ` per `Δ_κ` and `c = minorDiffC (m-1)` independent of `Ψ` and of `d`, so the layers `q ≥ 1` have `ρ ≍ Ψ`; `d` enters only through `Ψ ≥ W^{-d/2}` (paper `3_5:27`, D213), per-layer scale `W^{-d/2}` (RBM2D `W^{-1}`). Numerically (section (a)(iii), `d = 3`, `W = 2, 3, 4`): measured exponents of `rms |Δ^m|` for `m = 1, 2, 3` are `2.91, 4.29, 6.02` (small `u`) against `(m+1) d/2 = 3, 4.5, 6`, and the ratios `|Δ^m| / (2Ψ_ω)^{m+1}` stay below `0.25, 0.064, 0.021`, far below `C_m`. So `B ρ^q` with `B, ρ ≍ W^{-d/2}`, `ρ < 1`, is consistent with the data; the limit check of the owed premise is S1-26's.
- **Instances (b.4).** `d = 3`, `L = 3`, `W = 2`, `N = 216`, `E = 0`, `u = t = 1/31`, `ω = 0`, `M = 3`: `MinorGoodLe` is produced by `minorGoodLe_of_goodEvent_flow` from (4.1) at `ω = 0` with all hypotheses proved (`Ψ₀ = 1/30`, `8·3·Ψ₀ = 4/5`, `Ψ = 1/15`); the endpoint theorem is applied at `k = A` and three distinct rows `B, C, D` (`m = 3 = M`, tight); `diffBd_atom` at `r = 2`, `B + |T| = 3 = M` (tight); `bddMeas_…` at the word `Q_B P_C Q_D`. All 35 `inst_*` are proved with every deterministic hypothesis discharged, none assumed. The families are not constant (`inst_gEnt_nonconst`: `G^{(∅)}_{AA} = (31/30) i ≠ m`, `G^{({A})}_{AA} = 0`). Limitation: at `ω = 0` the matrix is diagonal, so by (a) the `Δ` themselves vanish and the bounds are trivially true there; a Lean sample with nonzero `Δ` would need an explicit nonzero `ω` (not attempted); (a)(iii) checks the nonzero case numerically.
- **Registry (DECISIONS §20, ST1-COMMON item 8).** The only new `Prop`-valued definition is `DiffBd`; theorems `DiffBd.delta/.shift/.mul/...` conclude it, so the scan does not list it as a premise, and the pre-check (b.7) exits 0 with no new premise. `MinorDiffGainUpTo'` stays registered as owed.

## (c) Verified Mathlib names (all by `#check` in `scratchpad/T2113/mathlib.lean`, 32 names, no error; names verified absent: none checked)
`Finset.insert_comm`, `Finset.card_insert_le`, `Finset.card_union_le`, `Finset.insert_union`, `Finset.union_insert`, `Finset.insert_eq_self`, `Finset.insert_eq_of_mem`, `Finset.card_insert_of_notMem`, `Finset.mem_insert_self`, `Finset.subset_insert`, `Finset.card_le_card`;
`List.nodup_cons`, `List.Nodup.sublist`, `List.Sublist.map`, `List.filter_sublist`, `List.eq_nil_of_length_eq_zero`;
`pow_le_pow_of_le_one`, `pow_le_pow_left₀`, `pow_le_pow_right₀`, `one_le_pow₀`, `pow_le_one₀`;
`Real.sqrt_sq`, `Real.norm_of_nonneg`, `Complex.norm_real`, `Complex.norm_I`, `Complex.I_ne_zero`, `Matrix.inv_eq_right_inv`, `dite_eq_left`, `dite_eq_right`, `norm_add_le`, `norm_mul`, `norm_pow`.

## (d) Open issues and paper-delta candidates
- **T2113a** (Lean/paper difference): the paper has no minor `G^{(S)}`, no difference of minors, no budget `M`, no constants `atomC`, `minorDiffC`, `2^n` of `DiffBd.mul`; it states `(GavLGEX)` at `3_5:33` and defers the proof to Lemma 4.1 of `[YY_25]` (`3_5:37`). The constants, the budget `M` and the side condition `Ψ ≤ 1` are Lean's construction; the statements are pointwise at one `ω` on `MinorGoodLe`. Dimension-free, same as in RBM2D (there tagged `T2158a`).
- **Registry comment (dispatcher).** `RBM3D/Test/Axioms.lean` (line 191, `RBM.Green.MinorDiffGainUpTo'`) says "proved by S1-25 `Green/MinorDiff`"; per the RBM2D source it is proved by S1-26 (`MinorDiffCond:869`). Editing an existing registry line is outside "append registry lines only", so it is left; the comment should read S1-26.
- RBM2D `HEAD` (`9e0f275`) differs from `c9a24cf` in this file (diff-stat in b.6); the port follows the ticket's `c9a24cf`, and `HEAD` was not compared statement by statement.
- No Lean instance with nonzero `Δ` (limitation above); no limit check is needed here, `MinorDiffGainUpTo'` is not a hypothesis of any theorem of this file.
