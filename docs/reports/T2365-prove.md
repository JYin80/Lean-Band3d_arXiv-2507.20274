Prover model: claude-sonnet-5-5

## (a) Math preflight — Fri Oct  9 23:12:59 UTC 2026

### (i) Exponent table and the map (G segments -> bundle fields)

`A` = `KLIndStepA.lean`, `B` = `KLIndStepB.lean` (worktree `t/T2365` = main 1fe7b7f). d = k+2, d >= 3, n >= 3, range: 3 <= L_i, 0 < g_i <= gmax, 0 <= t_i < 1. `Abar := g^2+|1-t| = g^2+1-t`.

| quantity | value in the proof | constraint | slack |
|---|---|---|---|
| loss, case (ii) (G2) | `L^{tau/3}` (f12, `B:548`) x `L^{tau/3}` (lattice sum `KLlat_pow_dim_rpow`) x `L^{tau/3}` (`arith2`) | product `= L^tau` (`hLt3`) | 0 (equality) |
| loss, case (ii) (G3) | 2 x f12 + 1 x `KLlat_pair_rpow`, each `L^{tau/3}` | product `= L^tau` | 0 |
| loss, (G0), case (i) | none | `1 <= L^tau` (`L >= 3`, `tau > 0`) | `3^tau - 1 > 0` |
| power of `B_{t,0}` | G0: `(2KB)^{n-2}`; G2: `(2KB)^{n-2}`; G3: `(2KB)^{n-3}` times `Abar^-1 <= B`; (i): `(K1 B)^{n-2}` | `n-2` | 0 (card `erase r = n-1`, one factor consumed) |
| weight `Q`, (G2) | `Q = d` (f2 carries `(|s|+1)^d`, `B:283`) | `Q <= 2(d-1)` (`SigSumZeroAbs`) | `d-2 >= 1` |
| weight `Q`, (G3) | `Q = 2(d-1)` (two f1 of exponent `d-1`, `B:348`) | `Q <= 2(d-1)` | 0 |
| signed estimate | `Q = 0` conjunct; `C_s (1-t)` | any `Q <= 2(d-1)` | none needed |
| (G0) cancellation | `rowSum (1-t)^-1` times signed `C_s (1-t)` (`KLIndStepB_G0`, `B:185-210`) | product exactly `C_s` | 0 (exact; a constant in `rowSum` would only rescale `C`) |
| f1 exponent | `(|s|+1)^{d-1}/(|y|+1)^{d-1}`, near `|s| <= |y|/2` from `diffOne` at c = 1/2; far from `zeroMode` and `1 <= 2^{d-1}((|s|+1)/(|y|+1))^{d-1}` | `|s| <= (|s|+1)^{d-1}` needs `d-1 >= 1`; `(|a|+1)^{-(d-2)} <= 1` needs `d-2 >= 0` | `d-2 >= 1` |
| f2 exponent | `(|s|+1)^d/(|y|+1)^d`; `diffTwo` at c = 1/2 | `|s|^2 <= (|s|+1)^d` needs `d >= 2` | `d-2 >= 1` |
| `(Abar)^-1 <= B_{t,0}` | `B = Abar^-1 + (L^d(1-t))^-1` (`KLlat_inv_le_Bparam`, generic in `d L g`) | `(L^d(1-t))^-1 >= 0` | instance: `B - Abar^-1 = 1/125/0.1 = 0.0800` |
| `B_{t,0} >= (gmax^2+1)^-1` | `Abar <= g^2 + 1 <= gmax^2 + 1` from `|1-t| <= 1`, `g <= gmax` (range) | `0 < g_i`, `0 <= t_i < 1` | instance: `2.937 >= 1/2` |
| uniformity | every constant of the 3 bundles is uniform in `i` (and in `s,s'`); `Q` takes two values, so 2 constants | `C` independent of `i` | 0 |
| `gmax` | enters only through `B >= (gmax^2+1)^-1` (case (i)); `ι` empty makes the target vacuous | none | no `0 < gmax` hypothesis is needed |
| `kappa` | absent from the abstract proof; `indStepTH_band` needs `|E| <= 2` from `|E| <= 2-kappa` (`thetaEdge_long`), so it takes `0 < kappa` like every band instance (`KLindStepAt_holds` has `hκ`) | `0 <= kappa` | not a bundle hypothesis |

Map (line numbers checked by `grep` on the branch):

| band use | replaced by |
|---|---|
| `A:142` `hPT.decay` (`Theta_norm_le`), `A:145` `Theta_apply_sub` | `decay` (`s ≠ s'`) with `Bparam_le_zero`, `exp <= 1` (`ellT > 0` from `L >= 3`); `transl` |
| `A:182-183` `diffOne (1/2)`, `zeroMode` (f1) | `diffOne τ` (c = 1/2 is built in), `zeroMode τ`; `A:195` `Theta_apply_sub` -> `transl` |
| `A:291-292` `diffTwo (1/2)`, `zeroMode` (f2) | `diffTwo τ`, `zeroMode τ`; `A:304` -> `transl` |
| `A:256, 353` `Theta0_apply_eq` (closed form `Theta0 = Theta - (L^d)^-1(1-t)^-1`) | not needed: `zeroMode` is `TH 0 a - c0`, `c0 := (L^{2d})^-1 ∑∑ TH` is independent of `a`, and the combinations `f1 = (TH(y+s)-TH(y-s))/2`, `f2 = (TH(y+s)+TH(y-s))/2 - TH(y)` have coefficient sums 0 (`1/2 - 1/2`, `1/2 + 1/2 - 1`), so `c0` cancels |
| `A:730` `KLSigmaPi_reflect` in `KLslice_f1_vanish` | `SigSumZeroAbs` conjunct 1 at `c = b+b`; `σ` is alternating at the only use (`B:735`), so the generic lemma takes `∀ j, σ j ≠ σ (j+1)` |
| `A:1062` `Theta_norm_le`, `A:1063` `hPT.short`, `A:1074, 1109` `Theta_apply_sub`, `A:1099` `thetaEdge_long`, `A:1070, 1105` `norm_mul_mSigma_lt_one` | `decay`+`transl`; `short`; `transl`; no rewriting (`TH` is the edge); not needed (`transl` is a field) |
| `A:1145` `KLmolecule_holds .. hPT.short` | `SigDecayAbs` (same shape as `KLmoleculeAt`: `C exp(-(c maxDist))`, every `σ`) |
| `A:1081` `(1+gmax^2)^-1 <= B` | `KLlat_inv_le_Bparam` + range (row above) |
| `B:283, 348` `KLsumZero_weighted` (Q = d, 2(d-1)), `B:546` `KLShort_holds` | `SigSumZeroAbs` conjunct 3 at those `Q`, `.2`; `KLShort` is no longer needed |
| `B:457` `KLf_crude_bound`, `B:471` `KLf12_bound` | generic crude and f12 from `decay`, `transl`, `diffOne`, `diffTwo`, `zeroMode` |
| `B:549` `A_sumZero_signed` | `SigSumZeroAbs` conjunct 3 `.1` (every root `r`, every `x`; the signed bound is given per slice, so `SumZero_sum_slice` is not needed) |
| `B:588` `thetaEdge_long`, `B:707` `sum_norm_Theta_row_le`, `B:735` `slice_f1_vanish` | `hσ j : σ j ≠ σ (j+1)` into the fields; `rowSum`; generic `slice_f1_vanish` |
| translation conjunct of `SigSumZeroAbs` | unused by the abstract step (it is used inside `KLsumZero_weighted`, `A:911`, band only); harmless extra hypothesis, pinned by K-b |

Band public names with no `hκ` in their statement (`KLIndStepA_Theta_norm_le`, `KLf0_bound`, `KLf_crude_bound`, `KLf12_bound`) cannot be wrapped through `indStepTH_band` (that needs `|E| <= 2`). They stay with their proofs, or the generic f12/crude lemmas are stated on one matrix family with the five fields (Theta for the band, `TH i s (!s)` for the bundle); no new hypothesis. `KLIndStepA_Theta_norm_le`, `KLindStep_nonAlt_noloss`, `KLindStepAt`, `KLindStepPin_holds`, `KLIndStepA_thetaEdge_long`, `KLlat_inv_le_Bparam`, `KLIndStepA_Bparam_*`, `KLIndStepA_Theta_apply_sub` are used outside the two files (grep); the dispatcher's check file `lake env lean docs/tickets/checks/T2365-check.lean` on the branch (before any edit): `exit=0`.

**N1: K-b numerics.** Model: BA molecule `Sigma^{(empty)}` (all trees without a long chord, leaf edges removed), K00 convention (`sigma_i` on `(a_{i-1}, a_i)`), `d = 1`, `W = 1`, `M` from `(self_m)` (circulant `Psi` on `Z_q`, `E = 0.3`), `Theta^{(ss')} = (1 - t M^{(ss')})^-1`; scripts are T2360's `kode.py`, `mgraph.py`, `molecule_full.py` copied (T2360 scratchpad) plus `n1.py`, `n1_table.py`. Both alternating `sigma`. `S_Q = max_{r,x} ∑_{δ_r=x} |Sigma| (maxDist+1)^Q`, distance cyclic on `Z_q` (= `zdistD` at `d = 1`).

```
$ cd <scratchpad>/T2365 && python3 n1_table.py
n=4 q=4 E=0.3: columns per 1-t in (1e-3 | 1e-4):  signed/(1-t);  S_Q/(g^2+1-t) for Q=1,2,4
 g=0.1  |  0.522;   3.583   6.800  32.824 |  0.522;   3.849   7.343  35.619
 g=0.2  |  0.552;   6.049  13.804  90.595 |  0.551;   6.165  14.083  92.507
 g=0.4  |  0.662;  10.805  28.910 230.711 |  0.662;  10.857  29.052 231.871
 g=0.8  |  0.881;   5.360  15.174 128.818 |  0.881;   5.365  15.189 128.940
n=4 q=5 E=0.3: ...
 g=0.1  |  0.522;   3.288   5.857  23.847 |  0.522;   3.528   6.317  25.848
 g=0.2  |  0.553;   5.180  10.895  61.630 |  0.553;   5.278  11.110  62.906
 g=0.4  |  0.680;  11.437  29.765 228.234 |  0.680;  11.493  29.913 229.398
 g=0.8  |  1.021;  10.216  29.228 250.293 |  1.021;  10.227  29.262 250.581
n=6 q=3 E=0.3: ...   (run time < 1 s)
 g=0.1  |  0.409;   2.990   5.275  18.984 |  0.409;   3.218   5.699  20.587
 g=0.2  |  0.466;   5.509  10.446  40.069 |  0.466;   5.621  10.663  40.916
 g=0.4  |  0.835;  20.579  40.983 163.408 |  0.836;  20.690  41.205 164.296
 g=0.8  |  4.441;  15.937  31.845 127.289 |  4.444;  15.963  31.895 127.489
STOP-LINE: max ratio(g=0.1)/ratio(g=0.4) over Q, 1-t, sigma, settings = 0.3545 (stop if > 2)
STOP-LINE: max reflection/translation defect = 6.67e-16 (stop if > 1e-10)
```

(`max |signed(+-) - signed(-+)|` <= 6.6e-13 in the three settings; both `sigma` give the same rows.) Supplementary, same script with `g in {0.01, 0.025, 0.05, 0.1, 0.4}`, `1-t = 1e-4`, `Q = 1, 2, 4`, `sigma = +-`: n=4 q=4: ratio `(g=0.01)` 1.795, 2.826, 9.046 against `(g=0.4)` 10.857, 29.052, 231.871; n=6 q=3, E=0: 1.334, 2.106, 6.738 against 11.660, 23.117, 91.858; stop-line statistics of the same script (g in 0.01..0.4 included): n=4 q=4 E=0.3: 0.3545; n=4 q=5 E=0: 0.2800; n=6 q=3 E=0: 0.2564; n=6 q=4 E=0.3: 0.1689; n=6 q=5 E=0.3: 0.1315 (all < 2). Result: the ratio `S_Q/(g^2+1-t)` decreases as `g` decreases (statistic <= 0.355), reflection and translation defects <= 1.6e-15, the signed sum `/(1-t)` is bounded (<= 4.45 at `g = 0.8`, n = 6, q = 3). The stop line is not triggered. This is `d = 1`, `W = 1` evidence on the `g`-scaling only; it is not a proof for `d >= 3`.

### (ii) One concrete nondegenerate instance

Data: `d = 3`, `L = 5`, `g = 1/2`, `E = 0`, `t = 9/10`, `kappa = gmax = 1`, `n = 4`, `ι = Unit`, `σ` alternating (the §7 data `KLinstPar`). `Theta_xi = (1 - xi S^B)^-1` on `Z_5^3` (125 sites), `S^B` from `sbKernel`; `m(+) = i`, so a long edge is `Theta_t` and a short edge is `Theta_{-t}`; `Sigma^{(empty)}` is the sum over the 3 trees of `n = 4` (`{}`, `{(0,2)}`, `{(1,3)}`; both chords have equal charges), `KLleafPar`/`KLnodePar` read from `KLTree.lean:75-81`; constants `C` of each field are the maxima of the ratios.

```
$ cd <scratchpad>/T2365 && python3 inst.py
S row sum [1. 1.]  symmetric 0.0
1-t=0.1, g^2+1-t=0.35, B_t0=2.93714, ell_t=1.581, m(+)=1j, m(+)m(-)=(1+0j), tm(+)^2=(-0.9+0j)
IndStepTH (tau=1, c=1):
  transl: 3.55271e-15            transl_short: 1.77636e-15
  rowSum: 10  (rowSum_minus_bound: 2.4869e-14, bound (1-t)^-1 = 10)
  C_decay: 1.60726   C_diffOne: 0.161781   C_diffTwo: 0.485343   C_zeroMode: 0.124427   C_short: 0.604803
sigma=+-+-: prod m = 1, support size 31125, max|Sigma| = 0.512      (sigma=-+-+: identical numbers)
  reflection defect 6.66e-15, translation defect 6.66e-15
  signed slice sum max = 0.05263 (= 1/19) -> C_signed = signed/(1-t) = 0.5263
  S_Q, C_Q = S_Q/(g^2+1-t), Q = 0..4: (1.4195, 4.0556) (2.69, 7.6857) (6.1496, 17.5704) (16.4997, 47.1419) (50.6214, 144.6325)
  SigDecayAbs: c=1, C = max |Sigma| e^(c maxDist) = 0.512
```

Every hypothesis of `indStepAbs_of` holds here with finite explicit constants: range (`3 <= 3`, `3 <= 4`, `3 <= 5`, `0 < 1/2 <= 1`, `0 <= 0.9 < 1`, `|E| = 0 <= 2 - 1`), `IndStepTH` (the `rowSum` is an equality, 10 = 10, slack 0), `SigDecayAbs`, `SigSumZeroAbs` (`Q <= 2(d-1) = 4`; weight range 0 to 4 covers the two `Q` used: 3 and 4). `Sigma` is nonzero (`max = 0.512`, signed slice sum `1/19`, matching the "at least `1/19`" of the existing §7 comment `KLIndStepA.lean:1379-1381`), `n = 4`, 125 sites, no collapsed window. The finite point check cannot test the `∃ C ∀ i` uniformity; that is the band statements (`KLPT`, `KLsumZero_weighted`, `KLmolecule_holds`) at the band instances. No external input is added: `hPT : KLPT d kappa gmax` stays a hypothesis of the band instances as in the existing §7 examples (gate PT), so there is no limit computation to add beyond the N1 `g`-scaling above.

### Verdicts

- Target 1 (pins `SigSumZeroAbs`, `SigDecayAbs`, `IndStepTH`, `IndStepAbs` verbatim): **PASS** (check file compiles, exit 0; shapes agree with `KLsumZero_weighted`, `KLmoleculeAt`, `KLPT` fields, and with `BAProp5to8`/`BATheta0` of `BA/FlowPins.lean:224`, `BA/MFixedPoint.lean:519`: the BA bundle has no loss and both charge pairs, so it implies `IndStepTH`).
- Target 2 (`KLindStepAt_iff`, `Iff.rfl`): **PASS**, by the check file's `KLindStepAt` expansion `example ... := Iff.rfl`; the `[∀ i, NeZero (L i)]` instance at `L := fun p => p.L` is for 1b to confirm.
- Target 3 (`indStepAbs_of`): **PASS**; no hypothesis beyond the three bundles and the range conjunction is needed (map above). Translation conjunct unused; band `KLslice_f1_vanish` is for every `σ`, the generic one needs `σ` alternating (the only use).
- Target 4 (`sigSumZeroAbs_band`, `sigDecayAbs_band`, `indStepTH_band`): **PASS**; `indStepTH_band` takes `0 < kappa` (see table), `short` is `KLShort` at `p.E` with `p.hE`.
- Target 5 (G1 re-derivation): **PASS**; no segment needs G3 (the `(T)` segments `KLSigmaPi_reflect`, `KLsumZero_weighted` stay unchanged).
- N1: no stop-line condition (statistic 0.3545 <= 2; defects <= 1.6e-15). No 1a RETURN.

### (b) Script output (commands and verbatim output; scratch files under the scratchpad T2365/)
```
$ date -u
Sat Oct 10 01:07:56 UTC 2026
$ git log --oneline 1fe7b7f..t/T2365
b74e5fd T2365: indStepAbs_of over the abstract bundles, band instances, KLindStepAt_holds via KLindStepAt_iff
82e412d T2365: KLIndStepA abstract bundles, generic leaf/f12/case (i), band instances
$ git diff --stat main...t/T2365
 RBM3D/Loop/KLIndStepA.lean | 809 +++++++++++++++++++++++++++-----------------
 RBM3D/Loop/KLIndStepB.lean | 820 +++++++++++++++++++++++++--------------------
 2 files changed, 955 insertions(+), 674 deletions(-)
$ wc -l, base 1fe7b7f vs branch (stop line: total 3121); import and banned-word counts
RBM3D/Loop/KLIndStepA.lean: base     1474, branch     1659
RBM3D/Loop/KLIndStepB.lean: base      947, branch     1043
total: base 2421, branch 2702; added/removed import lines: 0; sorry|admit|native_decide|axiom hits: 0
whole-declaration text equal to base 1fe7b7f: 6/6 (KLSigmaPi_reflect, KLsumZero_weighted, KLIndStepA_sumZero_signed, KLIndStepA_SigmaPi_add_const, KLIndStepA_thetaEdge_long, KLlat_sum_norm_Theta_row_le)
$ lake build   (full library in this worktree, single process; log scratchpad/T2365/full_build2.txt)
[4055/4173] Built RBM3D.Loop.KLIndStepA (10s)
[4056/4173] Built RBM3D.Loop.KLIndStepB (9.3s)
[4057/4173] Built RBM3D.Loop.KLInduct (10s)
[4058/4173] Built RBM3D.Loop.KLWardIneq (5.5s)
[4059/4173] Built RBM3D.Loop.KLFinal (3.4s)
Built RBM3D.Graph.LWExpCertS0 (592s)
Built RBM3D.Graph.LWExpCertS1 (602s)
Built RBM3D.Graph.LWExpCertBS0 (1592s)
Built RBM3D.Graph.LWExpCertBS1 (1805s)
Build completed successfully (4173 jobs).
exit=0
Sat Oct 10 01:07:48 UTC 2026
lines starting 'error' in the log: 0
$ lake env lean docs/tickets/checks/T2365-check.lean (on t/T2365)   exit=0 ; 'error' lines: 0
$ python3 pins.py   (whitespace-normalised text of the 4 pins, branch file vs check file)
SigSumZeroAbs  SAME  (KLIndStepA.lean, 817 chars) vs check file
SigDecayAbs    SAME  (KLIndStepA.lean, 295 chars) vs check file
IndStepTH      SAME  (KLIndStepA.lean, 1712 chars) vs check file
IndStepAbs     SAME  (KLIndStepB.lean, 536 chars) vs check file
$ example : @RBM.Loop.IndStepTH = @RBM.Loop.T2365Check.IndStepTH := rfl   -> error: Type mismatch (two distinct structures; the ticket's rfl protocol cannot hold for IndStepTH)
$ lake env lean <check file + 3 rfl pins + the substitute below>   exit=0 ; 'error' lines: 0
/-- `IndStepTH` is a `structure`: two distinct inductive types, so `rfl` between them is impossible;
the fields agree one by one (anonymous constructors in both directions). -/
example {ι : Type} (d : ℕ) (L : ι → ℕ) [∀ i, NeZero (L i)] (g t : ι → ℝ)
    (TH : ∀ i, Bool → Bool → Matrix (Zd d (L i)) (Zd d (L i)) ℂ) :
    RBM.Loop.IndStepTH d L g t TH ↔ RBM.Loop.T2365Check.IndStepTH d L g t TH :=
  ⟨fun h => ⟨h.transl, h.decay, h.short, h.diffOne, h.diffTwo, h.zeroMode, h.rowSum⟩,
   fun h => ⟨h.transl, h.decay, h.short, h.diffOne, h.diffTwo, h.zeroMode, h.rowSum⟩⟩
example : RBM.Loop.T2365Check.IndStepAbsOfStmt := by
  intro d n _ gmax ι L _ g t Sig TH hd hn hr hTH hD hS
  exact RBM.Loop.indStepAbs_of d n gmax L g t Sig TH hd hn hr
    ⟨hTH.transl, hTH.decay, hTH.short, hTH.diffOne, hTH.diffTwo, hTH.zeroMode, hTH.rowSum⟩ hD hS
```
```
$ lake env lean axioms.lean   (#print axioms of 23 declarations: 4 pins, KLindStepAt_iff, indStepAbs_of, 3 band instances, KLindStepAt_holds, KLindStepPin_holds, band wrappers, new KLIndStepA_* helpers)
exit=0 ; printed: 23 ; exactly [propext, Classical.choice, Quot.sound]: 23 ; sorryAx lines: 0
KLindStepAt_iff: [propext, Classical.choice, Quot.sound]
indStepAbs_of: [propext, Classical.choice, Quot.sound]
sigSumZeroAbs_band: [propext, Classical.choice, Quot.sound]
sigDecayAbs_band: [propext, Classical.choice, Quot.sound]
indStepTH_band: [propext, Classical.choice, Quot.sound]
KLindStepAt_holds: [propext, Classical.choice, Quot.sound]
$ public declaration names (non-private theorem/def/structure/...), base vs branch
KLIndStepA: base       38, branch       50; base only: []; branch only: [IndStepTH indStepTH_band KLIndStepA_crude_abs KLIndStepA_decay_le_zero KLIndStepA_f12_abs KLIndStepA_leaf_abs KLIndStepA_nonAlt_abs KLIndStepA_slice_vanish SigDecayAbs sigDecayAbs_band SigSumZeroAbs sigSumZeroAbs_band ]
KLIndStepB: base        5, branch        8; base only: []; branch only: [IndStepAbs indStepAbs_of KLindStepAt_iff ]
$ git grep -n -w -E '<the 15 new public names>' main -- 'RBM3D/*.lean' | wc -l     (same on t/T2356 t/T2358 t/T2361 t/T2362 t/T2366: 0 each)
       0
ports from RBM1D/RBM2D: none (re-parametrisations of this project's band proofs), so no RBM1D/RBM2D diff-stat
$ python3 stmt.py   (non-pin targets, from the branch files, up to ':='; the 4 pins are in the pins.py check above)
theorem KLindStepAt_iff (d n : ℕ) [NeZero n] (κ gmax : ℝ) :
    KLindStepAt d n κ gmax ↔
      IndStepAbs (ι := KLPar κ gmax) d n (fun p => p.L) (fun p => Bparam d p.L p.g p.t 0)
        (fun p σ δ => KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ)
        (fun p s s' => thetaEdge d p.L p.g (mSigma p.E) p.t s s') := Iff.rfl
theorem indStepAbs_of (d n : ℕ) [NeZero n] (gmax : ℝ) {ι : Type} (L : ι → ℕ) [∀ i, NeZero (L i)]
    (g t : ι → ℝ) (Sig : ∀ i, (Fin n → Bool) → (Fin n → Zd d (L i)) → ℂ)
    (TH : ∀ i, Bool → Bool → Matrix (Zd d (L i)) (Zd d (L i)) ℂ) (hd : 3 ≤ d) (hn : 3 ≤ n)
    (hr : ∀ i, 3 ≤ L i ∧ 0 < g i ∧ g i ≤ gmax ∧ 0 ≤ t i ∧ t i < 1) (hTH : IndStepTH d L g t TH)
    (hD : SigDecayAbs d n L Sig) (hS : SigSumZeroAbs d n L g t Sig) :
    IndStepAbs d n L (fun i => Bparam d (L i) (g i) (t i) 0) Sig TH := by
theorem sigSumZeroAbs_band (n : ℕ) [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) (hκ : 0 < κ) (hg : 0 < gmax) :
    SigSumZeroAbs (ι := KLPar κ gmax) d n (fun p => p.L) (fun p => p.g) (fun p => p.t)
      (fun p σ δ => KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ) :=
theorem sigDecayAbs_band (n : ℕ) [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) (hκ : 0 < κ) (hg : 0 < gmax) :
    SigDecayAbs (ι := KLPar κ gmax) d n (fun p => p.L)
      (fun p σ δ => KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ) :=
theorem indStepTH_band (hκ : 0 < κ) (hPT : KLPT d κ gmax) :
    IndStepTH (ι := KLPar κ gmax) d (fun p => p.L) (fun p => p.g) (fun p => p.t)
      (fun p s s' => thetaEdge d p.L p.g (mSigma p.E) p.t s s') := by
$ sed -n '1012,1039p' RBM3D/Loop/KLIndStepB.lean     (indStepAbs_of applied at ι = KLPar 1 1, then at KLinstPar)
/-- T2365, `indStepAbs_of` (target 3) applied to the three band bundles at `ι = KLPar 1 1`, `d = 3`,
`n = 4`, `gmax = 1` (`indStepTH_band`, `sigDecayAbs_band`, `sigSumZeroAbs_band`), then evaluated at the
§7 point `KLinstPar` (`L = 5`, `g = 1/2`, `E = 0`, `t = 9/10`): an alternating `σ` (root `1`, case (ii))
and `σ = (+,+,+,-)` (root `2`, case (i)).  `KLPT 3 1 1` is the only hypothesis left; the parameter
range, `3 ≤ d`, `3 ≤ n` and the bundles' band hypotheses are discharged. -/
example (hPT : KLPT 3 1 1) :
    ∃ C : ℝ, 0 < C ∧
      (∑ b : Zd 3 5, ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 1 = b),
          KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4) ∅ δ *
            ∏ i ∈ Finset.univ.erase (1 : Fin 4),
              thetaEdge 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4 i) (KLsigAlt 4 (i + 1))
                (![0, 1, 2, 3] i) (δ i)‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (4 - 2)) ∧
      (∑ b : Zd 3 5, ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 2 = b),
          KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) ![true, true, true, false] ∅ δ *
            ∏ i ∈ Finset.univ.erase (2 : Fin 4),
              thetaEdge 3 5 (1 / 2) (mSigma 0) (9 / 10) (![true, true, true, false] i)
                (![true, true, true, false] (i + 1)) (![0, 1, 2, 3] i) (δ i)‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (4 - 2)) := by
  obtain ⟨C, hC, H⟩ := indStepAbs_of 3 4 1 (fun p : KLPar 1 1 => p.L) (fun p => p.g) (fun p => p.t)
    (fun p σ δ => KLSigmaPi 3 p.L p.g (mSigma p.E) p.t σ ∅ δ)
    (fun p s s' => thetaEdge 3 p.L p.g (mSigma p.E) p.t s s') (by norm_num) (by norm_num)
    (fun p => ⟨p.hL, p.hg0, p.hg1, p.ht0, p.ht1⟩) (indStepTH_band one_pos hPT)
    (sigDecayAbs_band 4 (by norm_num) (by norm_num) one_pos one_pos)
    (sigSumZeroAbs_band 4 (by norm_num) (by norm_num) one_pos one_pos) 1 one_pos
  exact ⟨C, hC, H KLinstPar (KLsigAlt 4) 1 (by decide) ![0, 1, 2, 3],
    H KLinstPar ![true, true, true, false] 2 (by decide) ![0, 1, 2, 3]⟩

$ sed -n '1625,1628p;1645,1655p' RBM3D/Loop/KLIndStepA.lean     (the three band bundles at KLinstPar; statement lines 1629-1644 omitted here)
/-- T2365, the three band bundles (`indStepTH_band`, `sigDecayAbs_band`, `sigSumZeroAbs_band`) at the §7
data (`KLinstPar`, `n = 4`, `σ = σ^{(alt)}`, `a = (0, 1, 2, 3)`): translation and the row sum of a long
edge (`IndStepTH`), the decay (`SigDecayAbs`), the reflection and the `Q = 2(d-1) = 4` estimates on the
slice `δ_1 = 0` (`SigSumZeroAbs`).  `KLPT 3 1 1` is the only hypothesis left. -/
  have hTH := indStepTH_band (d := 3) (κ := 1) (gmax := 1) one_pos hPT
  have hD := sigDecayAbs_band (d := 3) (κ := 1) (gmax := 1) 4 (by norm_num) (by norm_num) one_pos one_pos
  have hS := sigSumZeroAbs_band (d := 3) (κ := 1) (gmax := 1) 4 (by norm_num) (by norm_num)
    one_pos one_pos
  obtain ⟨C, hC, c, hc, HD⟩ := hD
  obtain ⟨C', hC', HS⟩ := hS.2.2 4 (by norm_num)
  exact ⟨hTH.transl KLinstPar true false 1 2, hTH.rowSum KLinstPar true false (by decide) 0,
    ⟨C, hC, c, hc, HD KLinstPar (KLsigAlt 4) ![0, 1, 2, 3]⟩,
    hS.1 KLinstPar (KLsigAlt 4) (by decide) (1 + 1) ![0, 1, 2, 3],
    ⟨C', hC', HS KLinstPar (KLsigAlt 4) (by decide) 1 0⟩⟩

```

#### Narrative (every statement is backed by the output above or by the files)
1. Stage 1b started at `Fri Oct  9 23:13:05 UTC 2026` (first `date -u` of the stage). Section (a) was read and not edited; no mistake found, so there is no (a′).
2. Only the two sole writable files changed (diff stat above); no import line, `RBM3D.lean` or `Test/Axioms.lean` change.
3. `KLIndStepA` §5b (new, before §6): the pinned `SigSumZeroAbs`, `SigDecayAbs`, `IndStepTH` (text equal to the check file), the band instances `sigSumZeroAbs_band`, `sigDecayAbs_band`, `indStepTH_band`, and `KLIndStepA_f12_abs`.
4. `(eq:f12)`: the former private band lemmas `KLIndStepA_f1`/`_f2` became private cores `KLIndStepA_f1_core`, `_f2_core`, `_zero_key` for one matrix `T`, from `transl`, the near-range bound and the zero-mode bound against a free mean `c0`. No `Theta0_apply_eq` is needed: `f₁`, `f₂` have coefficient sum 0, so `c0` cancels. `KLf12_bound` (public, no `hκ`, statement unchanged) and `KLIndStepA_f12_abs` both call them.
5. Case (i): `KLIndStepA_leaf_abs` (from `short`, `decay`, `transl`, `B ≥ (1+gmax²)⁻¹`), `KLIndStepA_crude_abs`, `KLIndStepA_nonAlt_abs` (from `SigDecayAbs`); `KLindStep_nonAlt_noloss` is the band instance, `KLindStep_nonAlt` calls it unchanged. `KLIndStepA_decay_le_zero` is the tail of `KLIndStepA_Theta_norm_le` (statement unchanged).
6. `KLslice_f1_vanish` is the band instance of `KLIndStepA_slice_vanish`, which takes the reflection as a hypothesis (any `σ`); `indStepAbs_of` supplies it from conjunct 1 of `SigSumZeroAbs`.
7. `KLIndStepB`: `IndStepAbs` (text equal to the check file) and `KLindStepAt_iff` (`Iff.rfl`; the instance `[∀ i, NeZero (L i)]` at `L := fun p => p.L` is found, which (a) left for 1b). `KLIndStepB_G2sum/G3sum` use conjunct 3 of `SigSumZeroAbs` at `Q = k+2` and `Q = 2(k+1)`; `phi0/1/2` take a matrix; `KLIndStepB_alt_abs` (private) is the former `KLindStep_alt` proof over the bundles; `KLindStep_alt` is its band instance.
8. `indStepAbs_of` splits on `∀ j, σ j ≠ σ (j+1)`: alternating gives `C₁ L^τ B^{n-2}`; otherwise some `j ≠ r` is short and `C₂ B^{n-2} ≤ C₂ L^τ B^{n-2}` by `1 ≤ L^τ`; `C = C₁ + C₂`. `KLindStepAt_holds` is `(KLindStepAt_iff ..).2 (indStepAbs_of ..)` with unchanged statement; `KLindStepPin_holds` statement is the check file's Part 2 example (exit 0).
9. Hypotheses: none beyond the three bundles and the range conjunction. Of `SigSumZeroAbs` the proof uses conjunct 1 and conjunct 3 at `Q = 0` (signed), `k+2`, `2(k+1)`; conjunct 2 (translation) is unused, as (a) said. No `0 < gmax`, no nonempty `ι` and no `κ` is needed. The G3 fallback was not needed: no segment moved; the (T) segments are text-equal to the base (6/6 above).
10. Instances (both compile in the files, so the full build covers them): `KLIndStepB.lean:1012-1039` applies `indStepAbs_of` at `ι = KLPar 1 1`, `d = 3`, `n = 4` with the three band bundles and evaluates it at `KLinstPar` for an alternating `σ` (root 1) and `σ = (+,+,+,-)` (root 2); `KLIndStepA.lean:1625-1655` evaluates the three bundles at `KLinstPar`. `KLPT 3 1 1` is the only hypothesis left (gate PT); the older §7 examples are kept.
11. Size: base 2421, branch 2702 lines in total (stop line 3121); the first section commit 82e412d measured 2568 (`wc -l` in the tool log before that commit).

### (c) Verified Mathlib names (grep, file:line in `.lake/packages/mathlib/Mathlib`)
- new in this ticket: `mul_le_of_le_one_right` (Algebra/Order/GroupWithZero/Basic.lean:367).
- reused in new code: `inv_le_one_of_one_le₀` (:945), `one_le_pow₀` (:484), `pow_le_pow_right₀` (:501), `pow_le_pow_left₀` (:514), `le_self_pow₀` (:505), `le_mul_of_one_le_right` (:370), `inv_anti₀` (:1221), same file; `mul_inv_cancel₀` (Algebra/GroupWithZero/Defs.lean:227), `lt_max_of_lt_left` (Order/MinMax.lean:56); `Nat.sub_le` is core and compiles. No name was checked for absence.

### (d) Open issues and paper-delta candidates
1. Ticket protocol: `example : @RBM.Loop.IndStepTH = @RBM.Loop.T2365Check.IndStepTH := rfl` and `example : T2365Check.IndStepAbsOfStmt := @RBM.Loop.indStepAbs_of` cannot compile for any implementation, because `IndStepTH` is a `structure` and the check file's copy is a different inductive type (error above). The substitute in (b) (field-wise iff; `IndStepAbsOfStmt` proved from `indStepAbs_of` through it) compiles. The other three pins pass `rfl`. The auditor should use the substitute.
2. `indStepTH_band` takes `0 < κ` besides `hPT` (the ticket text lists `hPT` only): `KLPar` gives `|E| ≤ 2 - κ`, and `thetaEdge .. s s' = Θ_t` for `s ≠ s'` needs `|E| ≤ 2`. The other two band instances and `KLindStepAt_holds` carry `0 < κ` as well. This is an instance-level hypothesis, not a bundle hypothesis.
3. The bundles are the pins' choice: `IndStepTH` has properties 6, 7 at `c = 1/2` only (weaker than `KLPT`), `SigSumZeroAbs` is for alternating `σ` with `Q ≤ 2(d-1)` (D194). No new Lean/paper difference arises, so there is no paper-delta candidate `T2365a`.
4. Build log: a first full `lake build` in this worktree was started in two processes at once (`full_build.txt`: `Step6Kit.olean` "no such file") and discarded; the run reported above is the single-process `full_build2.txt` (started `Sat Oct 10 00:04:09 UTC 2026`, ended `01:07:48`, exit 0). It rebuilt modules unrelated to these files (LWExpCertS0/S1/BS0/BS1: 592/602/1592/1805 s).
