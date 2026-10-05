Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 16:25:10 UTC 2026

Scripts (python3/numpy, no Lean) in `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2196/`: `pre.py`, `shift.py`, `tab.py`. Conventions read from the files: `svarF = W^{-d} sbKernelR(blk i - blk j)` (`Gauss/FineModel.lean:47`), `sbKernelR x = [x=0](1+2dg²)⁻¹ + [zdistD x=1] g²(1+2dg²)⁻¹` (`Defs/Block.lean:74`), `green H z = (H - z)⁻¹` (`Green/EntryCore.lean:34`), `hwConst q = ((2q+1)(4q+2))^{q+1}` (`Green/IBPPoly.lean:721`).

### (i) Exponent table

| quantity | value | constraint | slack |
|---|---|---|---|
| `hwConst q` | 2, 324, 125000 at q=0,1,2 | `P(λV<\|Q\|²) ≤ hwConst q/λ^{q+1}` (target 5) | instance q=0: `2/4 = 1/2 < 1`, `2/(3-1)² = 1/2 < 1` (pin `T2196_inst_bounds`). q=1: `324/16 = 20.25`, `324/256 = 1.27` are trivial (>1): the nonempty instances use q=0 |
| `auxSizes d` | `L'≡3`, `W' s = max 1 (s/3)`, `lam'≡0` | `Sizes.three_le_L`: `3 ≤ 3`; `W_pos`: `max 1 _ ≥ 1` | `3 ≤ 3` (L' is tight, not used elsewhere) |
| slot `s = 3WL` | `W'(s) = max 1 (WL) = WL` | image of `auxEmb1 : Z_{WL} → Z_{3W'}`, `val a < WL = W'` | `a.val/W' = 0` for all `a < WL`: block 0 (script, 3 sizes). `a.val < 3W'`: slack factor 3 |
| aux dimension | `(3WL)^d`: 5832 at (3,3,2), 56623104 at (3,4,32), 104976 at (4,3,2) | block 0 has `W'^d = (WL)^d = N` points, all in the image | image = whole block 0 |
| `sbKernelR d L g 0` (target 2) | `(1+2dg²)⁻¹` (second summand: `zdistD 0 = 0 ≠ 1`) | `> 0` for every `d, g`; no `3 ≤ L`, no `3 ≤ d` | min over the test grid: `1.66e-3` at `(d,g)=(3,10)`; `1` at `g=0` (script (ii)) |
| `seqGvar auxSizes (auxRho c)` | `W'^{-d}` (diagonal), `W'^{-d}/2` (off-diagonal, `auxEmb` injective) at `lam'=0` | `> 0` on the image (needed for `auxScale = √(v/seqGvar)`) | 216·216 pairs at (3,3,2): all `0.004629630 = 6⁻³`. NOT positive off the image: `svarF((0,0,0),(6,0,0)) = 0` at `lam'=0` (neighbouring block), so the positivity is exactly "same block" (target 2) |
| `auxScale² · seqGvar = v` (target 3) | `v = mixVar g=1/2, a=b=1/2` | identity for every `v ≥ 0` (zeros allowed: scale 0) | max error 6.9e-18 over 30 pairs |
| row sum `∑_j Smix` (target 4) | `a·1 + b·N/N = a+b`, `N = (WL)^d = card Idx` | `3 ≤ L` (for `sum_sbKernelR`: `a + 2d·g²a = 1` needs `card nbhd = 2d`, 6 neighbours at `d=3, L=3`) | max error 2.7e-15 over 216 rows, g ∈ {0, 1/2, 2}, (a,b) = (.3,.9) |
| Hermitian shift `A` (target 6, 8) | `A.IsHermitian` only | `‖G^{(i)}‖ ≤ 1/\|Im z\|` and continuity of `green` need a Hermitian minor; `X` Hermitian (`Xmat_isHermitian`) | `A + X` Hermitian; `A` read by no row coordinate (script (iv): minor unchanged after resampling row/col 0 of `X`) |
| tag-free `v` (targets 6, 8) | `v(i,j,true) = v(i,j,false)` | `σ_ik = E\|X_ik\|² = 2 v(rowCoordF i k true)` needs equal tags | `gvarF`, `gueVar`, `mixVar` are tag-free (their definitions read `c.1 = c.2.1` and `c.1,c.2.1` only); `a,b<0` truncate to `0` by `toNNReal` |
| `kind_quad_tail` data | `v = a⁺ gvarF(K.lamV) + b⁺ gueVar`, `A = (K.M sz).mean n` | `A` Hermitian (`mean_herm`), `v` tag-free | at `UNKind.band 3`, `sz0`, n=0: `(L,W)=(4,32)`, `lamV = 1/64`, mean 0, `N = 2097152 = 2^21` (`Defs/Sizes.lean:260,267`) |
| §29 (1)-(7) | one law per statement; no `L`-`W` relation, no `∀ᶠ`, no lower bound on `N` or `lam`; the only scale is `N=(WL)^d` | every statement is non-asymptotic, uniform in `d,L,W,g,A,v` | not applicable (no exponent) |

d ≥ 3 limit bookkeeping (UN-25 takes no limit; `UNL32` and the LSY time scales are not touched). Consumer controls with `N=(WL)^d`, `max S_xy ≤ W^{-d}` (`sbKernelR ≤ 1`), `τ_U = c'/44`, `c' = 𝔠𝔡/30` (T2173-prove.md:21, `C_max = 21` from RBM2D, "to be redone at d=3" there). GUE row: Ward gives `N⁻²∑|G^{(i)}_{kl}|² = N⁻²η⁻¹∑Im G_kk`, error `(Im m^{(i)}/(Nη))^{1/2}`. Mixture row: `V ≤ σ_max (a+b) max_k Im G_kk/η`, `σ_max ≤ a W^{-d} + b N⁻¹`. Table (`python3 tab.py`, abridged to the lines used; `W ≥ N^𝔠` holds in all four rows):
```
(c,dd)=(1/6,1/10) (3,4,32) N=2097152 W^d=32768 N^c=11.31 c'=5.556e-4 tau_U=1.263e-05  1/N=4.768e-07 W^-d=3.052e-05
   eps=dd/3: eta=7.746e-07  1/(N eta)=6.156e-01  sqrt=7.846e-01  1/(W^d eta)=3.940e+01
   eps=1/2 : eta=6.905e-04  1/(N eta)=6.905e-04  sqrt=2.628e-02  1/(W^d eta)=4.419e-02
   t*=N^(-1+tau_U)=4.769248e-07 a=e^-t*=0.999999523 b=4.769e-07; sigma_max<=3.0518e-05 (W^-d=3.0518e-05)
(c,dd)=(1/6,1/10) (3,5,32) N=4096000 N^c=12.65  eps=dd/3: 1/(N eta)=6.020e-01 1/(W^d eta)=7.525e+01 | eps=1/2: 1/(N eta)=4.941e-04 1/(W^d eta)=6.176e-02 | t*=2.441876e-07
(c,dd)=(1/10,1/20) (3,4,32) N^c=4.29 c'=1.667e-4 tau_U=3.788e-06  eps=dd/3: 1/(N eta)=7.846e-01 1/(W^d eta)=5.021e+01 | eps=1/2: 6.905e-04, 4.419e-02 | t*=4.768635e-07
(c,dd)=(1/10,1/20) (3,5,32) N^c=4.58  eps=dd/3: 1/(N eta)=7.759e-01 1/(W^d eta)=9.698e+01 | eps=1/2: 4.941e-04, 6.176e-02 | t*=2.441547e-07
```
Reading for the consumers: at `η = N^{-1+𝔡/3}` the crude mixture bound `σ_max/η ≈ (W^dη)⁻¹ ≫ 1` (39.4 to 97.0) and the GUE factor `(Nη)⁻¹` is 0.60 to 0.78; both are asymptotic-only statements (`N^{-ε}` decay) and no UN-25 statement uses them. At `η = N^{-1/2}` they are 0.044 to 0.062 and 5e-4 to 7e-4. At the OU end time `a + b = 1`, `σ_max = a W^{-d} + b/N = 3.0518e-05 = W^{-d}` to 5 digits (`b/N ≈ 2e-13`).

### (ii) One concrete nondegenerate instance

Instance: `d=3, L=3, W=2` (`N = 216`) for the carrier, row sums and all `inst_*`; `d=3, L=3, W=1` (`N=27`) for the shift Monte Carlo; `z = 0.3+0.1i` (script) / `Complex.I` (Lean instances). Hypotheses at the instance: `NeZero 3`, `NeZero 2`; `3 ≤ L`: `3 ≤ 3`; `z.im ≠ 0`: `0.1 ≠ 0`; `0 < λ`: `λ = 4, 16`; `1 < Λ`: `Λ = 3`; tag-free `v`: `mixVar`/`gueVar`; `A` Hermitian: `A = 0, 1, mean`, and the random Hermitian `A` of the script; `a = b = 1/2` (>= 0); `lam = 0` for the aux sizes; no `N=0`, no empty index set (`card Idx = 216`, `27`), collapsed window none.
```
$ python3 pre.py            (carrier, constants, row sums; verbatim excerpts)
hwConst q=0,1,2: [2, 324, 125000] ; hw0/4= 1/2 ; hw0/(3-1)^2= 1/2
(d,L,W)=(3, 3, 2) slot=18 W'=6 (=WL:True) L'=3 aux dim=(3WL)^d=5832; block-0 side W'=6; max_a a.val//W' over a<WL: 0 ; max a.val < 3W'? True
(d,L,W)=(3, 4, 32) slot=384 W'=128 (=WL:True) ... aux dim=56623104 ... max_a a.val//W' over a<WL: 0 ; max a.val < 3W'? True
(d,L,W)=(4, 3, 2) slot=18 W'=6 (=WL:True) ... aux dim=104976 ... max_a a.val//W' over a<WL: 0 ; max a.val < 3W'? True
   g=0 sbKernelR(0)=1 | g=1/64: 0.9985372989 | g=1: 0.1428571429 | g=10: 0.001663893511   (all = 1/(1+2dg^2), pos=True, d=3; d=4: 1, 0.998050682, 0.111111111, 0.00124843945)
(3,3,2): pairs on image 46656 distinct svarF(lam=0) values {0.00462962962963} W'^-d= 0.004629629629629629 ; seqGvar diag= 0.004629629629629629 offdiag= 0.0023148148148148147
   contrast (not on image, aux lattice Z_18^3), lam=0: svarF((0,0,0),(6,6,6))= 0.0 svarF((0,0,0),(6,0,0))= 0.0
auxScale^2*seqGvar-v max err (30 pairs): 6.938893903907228e-18
neighbours of 0 in Z_3^3: 6 =2d= 6
g=0: max_i |sum_j svarF-1|=0.00e+00; max_i |sum_j Smix(a=.3,b=.9)-(a+b)|=2.66e-15
g=0.5: max_i |sum_j svarF-1|=1.22e-15; max_i |sum_j Smix(a=.3,b=.9)-(a+b)|=2.44e-15
g=2: max_i |sum_j svarF-1|=4.44e-16; max_i |sum_j Smix(a=.3,b=.9)-(a+b)|=2.44e-15
$ python3 shift.py          (target 6: d=3,L=3,W=1,N=27, v=mixVar g=0 a=b=1/2 so sigma_0k=1/54 off-diagonal, random Hermitian A, z=0.3+0.1i, row 0)
Schur identity |1/G_ii - [(A+X)_ii - z - sum (A+X)_ik G^(i)_kl (A+X)_li]| = 1.1050065994108394e-15
split check |sum(A+X)G(A+X) - (xx+xa+ax+aa)| = 2.482534153247273e-16
minor (A+X)^(0) unchanged after resampling row/col 0 of X: True
MC Ns=10000: E[Q]=-0.0009+0.0006j (std err 0.0022); E|Q|^2/E[V]=1.0137 (<= hwConst0=2)
q=0 lam=4: P(lam*V<|Q|^2)=0.0405  bound 0.5000  emp<=bound: True
q=0 lam=16: P(lam*V<|Q|^2)=0.0021  bound 0.1250  emp<=bound: True
q=1 lam=4: 0.0405  bound 20.2500 (trivial, >1) | q=1 lam=16: 0.0021  bound 1.2656 (trivial, >1)
```
Split of the Schur term (`xx`, `xa`, `ax`, `aa` of `shift.py`): `xx = ∑X_ik G_kl X_li` is the quadratic chaos of target 6 (`Q = xx - ∑σ_ik G_kk`); `xa = ∑_k X_ik c_k`, `c = G^{(i)}A_{·i}`, and `ax = ∑_l d_l X_li`, `d = A_{i·}G^{(i)}` (`X_li = conj X_il`, so it is the conjugate-type rank-one chaos with coefficient `conj d`), are the rank-one terms of target 9; `aa = ∑A_ik G_kl A_li` reads no row coordinate. In all four terms `G^{(i)}` is the minor resolvent of `A + X`, which reads only `A` and the coordinates `(k,l,·)` with `k,l ≠ i`.

External hypotheses: none (every merged input is a Lean theorem; `GaussIBP sz` is discharged by the merged `gaussIBP sz`, `Green/IBPPoly.lean:305`). No limit computation applies (UN-25 states no asymptotic hypothesis).

### Verdict per target (mathematics only)
- 1 auxiliary carrier (`auxSizes d`, `auxSlot`, `auxEmb` coordinatewise, `auxRho`): PASS (blocks, injectivity and dimension count verified above; `lam' = 0` is a constant, `S^{(B)}(0) = I`).
- 2 positivity `svarF_pos_of_block_eq`, `svarF_aux_pos`, `seqGvar_aux_rho_pos`: PASS (`sbKernelR 0 = (1+2dg²)⁻¹ > 0` for every `d, g`).
- 3 realisation (`auxT_law`, `auxHG_law`, `exists_seqP_map_eq_gaussLaw`): PASS (scale identity `s² · seqGvar = v` verified; zero variances allowed).
- 4 variance families (`gaussLaw`, `mixVar`, `Smix`, `sum_Smix_row`, `TagFree`, `mixVar_tagFree`): PASS (row sum `a+b`; `mixVar` tag-free; `ouVar` is `mixVar g (e^{-t}) (1-e^{-t})` after `toNNReal`, definitional per `OU.lean:56`).
- 5 `chaos_tail`: PASS (`E[(|Q|²/V_q)^{q+1}] ≤ hwConst q`, merged `mom_le_momVpow`; Markov at `λ`).
- 6 `gaussLaw_quad_tail` with shift: PASS (the shifted minor is off-row: script (iv); `E|Q|²/E[V] = 1.014 ≤ 2`, `E Q ≈ 0`).
- 7 `gue_quad_tail`: PASS (`σ_ik = 2·(2N)⁻¹ = N⁻¹`, `A = 0`, matches the pin's `(N⁻¹)²∑|G|²` and `N⁻¹∑G_kk`).
- 8 `kind_quad_tail`: PASS (`A = mean` Hermitian by `mean_herm`; `v` tag-free).
- 9 `aux_lin_tail`: PASS (`Q = Y - R`, `V_q = R²`, Markov with `(Λ-1)²`; numbers `2/4 = 1/2` at `Λ = 3, q = 0`; the rank-one structure of the Schur cross terms checked in (iv)).
- Instances (`inst_*`): all hypotheses are deterministic and hold at the data above; `inst_kind_quad_tail_band` uses `sz0` at `n` kept variable (`(L,W) = (4,32)` at `n=0`).

## (b) Script output (stage 1b, Mon Oct  5 16:40:59 UTC 2026; worktree RBM3D-wt/T2196, branch t/T2196, commit a726626)

No (a′): nothing in (a) was found wrong. `$S` below = the scratchpad subdirectory T2196/ (pins.lean, cmp.py, extract.py, names.txt, registry.lean, axioms.lean, mathlib.lean).

```
$ git diff --stat main...t/T2196
 RBM3D/Universality/GUEPhase/AuxCarrier.lean | 1364 +++++++++++++++++++++++++++
$ lake build RBM3D.Universality.GUEPhase.AuxCarrier 2>&1 | tail -1     (tool log after the last edit: "✔ [3357/3357] Built ...AuxCarrier (5.2s)")
Build completed successfully (3357 jobs).
$ lake build            (full library; the module is not in RBM3D.lean, the hub adds the root import at merge)
Build completed successfully (3999 jobs).                                exit=0
$ grep -cE "sorry|admit|native_decide|^axiom " RBM3D/Universality/GUEPhase/AuxCarrier.lean
0
```
Registry pre-check (ticket paragraph "Sole writable files"): temporary file outside the repo, `import RBM3D` + `import RBM3D.Universality.GUEPhase.AuxCarrier` + `#assert_rbm_axioms`:
```
$ lake env lean $S/registry.lean > $S/registry.out 2>&1; echo "exit=$?"; sed -n 1p $S/registry.out; grep -c TagFree $S/registry.out
exit=0
axiom audit: 5748 theorems, 2054 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
0
```
`RBM.Univ.TagFree` is not flagged (the checker flags a premise only if no theorem concludes it; `gueVar_tagFree`, `gvarF_tagFree`, `mixVar_tagFree` conclude it); `RBM3D/Test/Axioms.lean` is not touched.

### Axioms (`#print axioms` of the 105 public declarations, 90 in `RBM.Univ`, 15 in `RBM.Univ.AuxCarrierCheck`; 5 private helpers)
```
$ lake env lean $S/axioms.lean | <group by axiom set>
104 declarations with axioms [propext, Classical.choice, Quot.sound]
1 declarations with axioms none: ['RBM.Univ.auxSlot']
$ ... | grep targets
'RBM.Univ.svarF_pos_of_block_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.exists_seqP_map_eq_gaussLaw' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.sum_Smix_row' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.chaos_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.gaussLaw_quad_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.gue_quad_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.kind_quad_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.aux_lin_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.AuxCarrierCheck.inst_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
```
### Target statements (`python3 extract.py <names>`: file line, then the text up to `:=`; `sum_Smix_row` sits in a section with `variable (d L W : ℕ) [NeZero L] [NeZero W]`)
```
135: theorem svarF_pos_of_block_eq (d L W : ℕ) [NeZero L] [NeZero W] (g : ℝ) (i j : Idx d L W)
    (h : (split d L W i).1 = (split d L W j).1) : 0 < svarF d L W g i j :=
259: theorem exists_seqP_map_eq_gaussLaw (d L W : ℕ) [NeZero L] [NeZero W] (v : CoordF d L W → ℝ≥0) :
    ∃ (sz : Sizes d) (T : Sizes.SeqΩ sz → Ω d L W), Continuous T ∧
    (Sizes.seqP sz).map T = Measure.infinitePi (fun c : CoordF d L W => gaussianReal 0 (v c)) :=
304: theorem sum_Smix_row (hL : 3 ≤ L) (g a b : ℝ) (i : Idx d L W) :
    ∑ j : Idx d L W, (a * svarF d L W g i j + b / (((W * L) ^ d : ℕ) : ℝ)) = a + b :=
500: theorem chaos_tail (C : RowChaos sz κ) {lam : ℝ} (hlam : 0 < lam) (q : ℕ) :
    (Sizes.seqP sz) {ω | lam * C.Vq ω < ‖C.chaos ω‖ ^ 2}
    ≤ ENNReal.ofReal (hwConst q / lam ^ (q + 1)) :=
918: theorem gaussLaw_quad_tail {v : CoordF d L W → ℝ≥0} (hv : TagFree d L W v)
    {A : Matrix (Idx d L W) (Idx d L W) ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (i : Idx d L W) {lam : ℝ} (hlam : 0 < lam) (q : ℕ) :
    gaussLaw d L W v {s | lam * quadVqS d L W v A z i s < ‖quadQS d L W v A z i s‖ ^ 2}
    ≤ ENNReal.ofReal (hwConst q / lam ^ (q + 1)) :=
959: theorem gue_quad_tail {z : ℂ} (hz : z.im ≠ 0) (i : Idx d L W) {lam : ℝ} (hlam : 0 < lam) (q : ℕ) :
    gueP d L W {s | lam * ((((((W * L) ^ d : ℕ) : ℝ))⁻¹) ^ 2 *
    ∑ k : {a : Idx d L W // a ≠ i}, ∑ l : {a : Idx d L W // a ≠ i},
    ‖green ((Xmat d L W s).submatrix Subtype.val Subtype.val) z k l‖ ^ 2) <
    ‖(∑ k : {a : Idx d L W // a ≠ i}, ∑ l : {a : Idx d L W // a ≠ i},
    Xmat d L W s i k.1 * green ((Xmat d L W s).submatrix Subtype.val Subtype.val) z k l *
    Xmat d L W s l.1 i) -
    ((((W * L) ^ d : ℕ) : ℝ))⁻¹ * ∑ k : {a : Idx d L W // a ≠ i},
    green ((Xmat d L W s).submatrix Subtype.val Subtype.val) z k k‖ ^ 2}
    ≤ ENNReal.ofReal (hwConst q / lam ^ (q + 1)) :=
982: theorem kind_quad_tail (K : UNKind d) (sz : Sizes d) (n : ℕ) (a b : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (i : Idx d (sz.L n) (sz.W n)) {lam : ℝ} (hlam : 0 < lam) (q : ℕ) :
    gaussLaw d (sz.L n) (sz.W n) (mixVar d (sz.L n) (sz.W n) (K.lamV sz n) a b)
    {s | lam * quadVqS d (sz.L n) (sz.W n) (mixVar d (sz.L n) (sz.W n) (K.lamV sz n) a b)
    ((K.M sz).mean n) z i s <
    ‖quadQS d (sz.L n) (sz.W n) (mixVar d (sz.L n) (sz.W n) (K.lamV sz n) a b)
    ((K.M sz).mean n) z i s‖ ^ 2}
    ≤ ENNReal.ofReal (hwConst q / lam ^ (q + 1)) :=
1184: theorem aux_lin_tail {d : ℕ} {sz : Sizes d} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (C : RowChaos sz κ) (Y R : Sizes.SeqΩ sz → ℝ) (hR0 : ∀ ω, 0 ≤ R ω)
    (hchaos : ∀ ω, C.chaos ω = ((Y ω - R ω : ℝ) : ℂ)) (hV : ∀ ω, C.Vq ω = R ω ^ 2)
    {Λ : ℝ} (hΛ : 1 < Λ) (q : ℕ) :
    (Sizes.seqP sz) {ω | Λ * R ω < Y ω}
    ≤ ENNReal.ofReal (hwConst q / ((Λ - 1) ^ 2) ^ (q + 1)) :=
1357: theorem inst_bounds :
    hwConst 0 / (4 : ℝ) ^ (0 + 1) = 1 / 2 ∧
    hwConst 0 / (((3 : ℝ) - 1) ^ 2) ^ (0 + 1) = 1 / 2 :=
```
### Pins of the check file: one `example : T2196Check.<pin> := fun … => <target> …` each
`pins.lean` = `import RBM3D.Universality.GUEPhase.AuxCarrier` + check-file lines `/-! ## 2. Pinned statements -/` … before the first `#check (RBM.Univ.T2196Check.` (copied verbatim by script) + these examples (the 3 binder-order-sensitive ones adapt `{d L W} {v} {A}` to the pin's explicit binders):
```
$ lake env lean $S/pins.lean; echo "exit=$?"          → exit=0     (negative control: with `hlam (q+1)` in the `gue_quad_tail` example the file fails: heartbeat timeout error)
example : T2196_svarF_pos_of_block_eq := fun d L W _ _ g i j h => svarF_pos_of_block_eq d L W g i j h
example : T2196_exists_seqP_map_eq_gaussLaw := fun d L W _ _ v => exists_seqP_map_eq_gaussLaw d L W v
example : T2196_sum_Smix_row := fun d L W _ _ hL g a b i => sum_Smix_row d L W hL g a b i
example : T2196_chaos_tail := fun {d} {sz} {κ} _ _ C {lam} hlam q => chaos_tail C hlam q
example : T2196_gaussLaw_quad_tail := fun d L W _ _ v hv A hA z hz i lam hlam q => gaussLaw_quad_tail hv hA hz i hlam q
example : T2196_gue_quad_tail := fun d L W _ _ z hz i lam hlam q => gue_quad_tail hz i hlam q
example : T2196_quad_tail_kind := fun {d} K sz n a b z hz i lam hlam q => kind_quad_tail K sz n a b hz i hlam q
example : T2196_aux_lin_tail := fun {d} {sz} {κ} _ _ C Y R hR0 hch hV Λ hΛ q => aux_lin_tail C Y R hR0 hch hV hΛ q
example : T2196_inst_bounds := AuxCarrierCheck.inst_bounds
```
### Compiled nonempty instances (namespace `RBM.Univ.AuxCarrierCheck`, same file; `d = 3, L = 3, W = 2`, `N = 216`, `z = Complex.I`, row `0`; all in the build above)
```
$ grep -n "^theorem inst_" RBM3D/Universality/GUEPhase/AuxCarrier.lean | sed 's/ :.*//;s/(.*//'      (15 theorems)
1218 inst_svarF_pos_of_block_eq   1226 inst_aux_pos   1232 inst_auxT_law   1238 inst_auxHG_law   1244 inst_exists_seqP_map_eq_gaussLaw
1252 inst_chaos_tail   1263 inst_gue_quad_tail   1279 inst_band_quad_tail   1290 inst_shift_quad_tail   1302 inst_kind_quad_tail_band
1319 inst_kind_quad_tail_band_size   1327 inst_aux_lin_tail   1344 inst_sum_Smix_row   1350 inst_mixVar_exp_eq_ouVar   1357 inst_bounds
$ python3 extract.py inst_shift_quad_tail inst_aux_lin_tail       (hypotheses: `Matrix.isHermitian_one`, tag-free `rfl`, `Complex.I.im ≠ 0` by `simp`, `0 < 4`, `1 < 3`: all discharged)
1290: theorem inst_shift_quad_tail :
    gaussLaw 3 3 2 (mixVar 3 3 2 0 (1 / 2) (1 / 2)) {s |
    4 * quadVqS 3 3 2 (mixVar 3 3 2 0 (1 / 2) (1 / 2)) 1 Complex.I 0 s <
    ‖quadQS 3 3 2 (mixVar 3 3 2 0 (1 / 2) (1 / 2)) 1 Complex.I 0 s‖ ^ 2}
    ≤ ENNReal.ofReal (hwConst 0 / 4 ^ (0 + 1)) :=
1327: theorem inst_aux_lin_tail :
    (Sizes.seqP (auxSizes 3)) {ω | 3 * (∑ k : {a : Idx 3 3 2 // a ≠ 0},
    sigRow 3 3 2 (gueVar 3 3 2) 0 k.1 * ‖(1 : ℂ)‖ ^ 2) <
    ‖∑ k : {a : Idx 3 3 2 // a ≠ 0}, auxHG 3 3 2 (gueVar 3 3 2) ω 0 k.1 * (1 : ℂ)‖ ^ 2}
    ≤ ENNReal.ofReal (hwConst 0 / ((3 - 1) ^ 2) ^ (0 + 1)) :=
1302: theorem inst_kind_quad_tail_band (n : ℕ) (i : Idx 3 (SizesInst.sz0.L n) (SizesInst.sz0.W n)) :     (n, i variables; body: `kind_quad_tail (UNKind.band 3) SizesInst.sz0 n (1/2) (1/2) …`)
1357: theorem inst_bounds : hwConst 0 / (4:ℝ)^(0+1) = 1/2 ∧ hwConst 0 / (((3:ℝ)-1)^2)^(0+1) = 1/2     (bounds 1/2 < 1; `inst_kind_quad_tail_band_size`: sz0.L 0 = 4, sz0.W 0 = 32, sz0.size 0 = 2^21)
```
### Comparison with RBM2D `AuxCarrier.lean` at c9a24cf (`python3 cmp.py src.lean AuxCarrier.lean`; statements up to `:=`, with `d L W`/`L W`, `[NeZero _]`, `CoordF/svarF/gvarF/PF`, `^ 2`/`^ d`, `{d : Sizes}`/`sz` normalised)
```
source declarations: 85 | mine: 90      identical after renaming: 56      not ported: svar_aux_pos (replaced by svarF_pos_of_block_eq + svarF_aux_pos), P_eq_gaussLaw (now PF_eq_gaussLaw), card_Idx (merged RBM.Gauss.card_Idx)
new in mine: split_auxEmb_fst svarF_pos_of_block_eq svarF_aux_pos exists_seqP_map_eq_gaussLaw PF_eq_gaussLaw gvarF_tagFree mixVar_tagFree kind_quad_tail
differing (26), by cause:
  Idx d (coordinatewise embedding, target 1): auxEmb
  coupling g (target 4): mixVar Smix mixVar_exp_eq_ouVar Smix_symm Smix_nonneg sum_Smix_col mixVar_zero_right mixVar_zero_left sum_Smix_row (also: statement unfolded as in the pin)
  shift A, hA (targets 6, 8): auxMinorRes norm_auxMinorRes_le continuous_auxMinorRes auxMinorRes_congr auxQuadChaos auxQuadChaos_sg auxQuadChaos_h auxQuadChaos_chaos
     auxQuadChaos_Vq quadVqS quadQS continuous_green_minorS continuous_quadVqS continuous_quadQS auxQuadChaos_eq gaussLaw_quad_tail
second pass (delete from mine the shift A/hA, the coupling g, Idx d of auxEmb): 3 still differ: sum_Smix_row (unfolded pin form), sum_Smix_col (a `: Idx` binder ascription), continuous_green_minorS (regex artefact `(A + Xmat s)`)
```
Identical after renaming (56; `auxSizes` additionally has the field `lam _ := 0`, in its body, not in the compared text): auxSizes auxSlot auxW_slot auxL auxEmb1 auxEmb1_val auxEmb1_injective blk_auxEmb1 auxEmb_injective auxRho auxRho_injective seqGvar_aux_rho_pos aux_infinitePi_map_comp auxScale auxT auxT_measurable auxScale_sq auxT_law auxHG auxHG_law gaussLaw gueP_eq_gaussLaw RowChaos_continuous_Vq RowChaos_Vq_congr chaosEps chaosEps_chaos chaosEps_Vq chaosEps_Vq_le_one chaosEps_mom_le chaos_tail_eps chaos_tail rowCoordF rowSignF Xentry_eq_rowCoordF rowCoordF_injOn TagFree seqGvar_auxRho_tag auxScale_tag auxHG_apply lamRow lamRow_nonneg continuous_auxT continuous_auxHG auxHG_isHermitian auxOffRow Xentry_congr_offRow sigRow auxHG_swap continuous_Xmat_apply gueVar_tagFree sigRow_gueVar gue_quad_tail auxLinChaos auxLin_chaos auxLin_Vq aux_lin_tail
### Name-clash grep and port citations
```
$ for each of the 105 public names: git grep -n -w <name> main -- RBM3D        (main = d783ee3)
names 105, total hits on main under RBM3D/: 0
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h               → 9e0f275 (HEAD);  source read at c9a24cf (1183 lines)
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Universality/GUEPhase/AuxCarrier.lean
 RBM2D/Universality/GUEPhase/AuxCarrier.lean | 216 ++++++----------------------   (46 insertions(+), 170 deletions(-))
$ git -C ../RBM1D --no-optional-locks log -1 --format=%h               → de0de42  (no RBM1D file was read or copied: its pieces reach this file only through the RBM2D port)
```

Narrative (facts from the file and the logs above):
- One new file, 1364 lines, imports exactly PinsK, OU, Green.IBP, Induction.ConArgDet, Gauss.Domination; sections §2, §3, §6b, §6c, AuxLin, instances. No hypothesis added to any target, no pin changed, no `3 ≤ d` used anywhere; `3 ≤ L` only in `sum_Smix_row` (needed by `IBP_sum_svarF_row`).
- Target 1: `auxSizes d` has `lam _ := 0`; `auxEmb1`, `auxEmb`, `auxRho` and all aux names take explicit `d` (the coordinate type is `ZMod ((auxSizes d).W slot * (auxSizes d).L slot)`); `split_auxEmb_fst` shows every image point is in block `0`.
- Target 2: `svarF_pos_of_block_eq` is `sbKernelR d L g 0 = (1 + 2 d g²)⁻¹` (`simp [sbKernelR]`, `zdistD_zero`) plus positivity of `(W^d)⁻¹`: no `sbSupport`, no `3 ≤ L`; `svarF_aux_pos`, `seqGvar_aux_rho_pos` follow as in the source.
- Target 4: `mixVar_exp_eq_ouVar` and `mixVar_tagFree`, `gueVar_tagFree`, `gvarF_tagFree` are `rfl`; `gueP_eq_gaussLaw`, `PF_eq_gaussLaw` are `rfl`. `sum_Smix_row` is stated in the pin's unfolded form (`∑ j, (a * svarF … + b / N) = a + b`), `Smix` is the folded name.
- Target 6: the shift enters only through `auxMinorRes = green ((A + auxHG v ω).submatrix …) z`; `auxMinorRes_congr` has the source's argument (`A` reads no coordinate; one extra `congr 1` for `Matrix.add_apply`); `quadQS` keeps the row entries `Xmat s i k`, `Xmat s l i` of the centred `X`. `A.IsHermitian` is the only property of `A` used (norm bound, continuity).
- Binder shapes: `gaussLaw_quad_tail`, `gue_quad_tail` have `{d L W}` implicit (as the source has `L W` implicit), `v`, `A` implicit (determined by `hv`, `hA`); `auxQuadChaos d L W v hA hz i` has `{A}` implicit. The pin examples above adapt these to the pins' explicit binders.
- Private helpers (5): `auxCarrier_Xmat_apply` (`rfl`; the merged helper `fineModel_Xmat_apply` is private), `auxCarrier_Gres_true`, `auxCarrier_norm_green_apply_le` (pattern of the private `LDEQuadInst_norm_green_apply_le`, via `RBM.Ind.Gres_eq_green_zSig`, `norm_Gsig_le_inv_eta`, `RBM.Ind.norm_apply_le_l2_opNorm`), `auxLin_sg_lam`, `auxLin_h_lam` (the source's private pair).
- `chaosEps_mom_le` keeps the source's explicit constant `((2q+1)(4q+2))^(q+1)`; `chaos_tail_eps` uses it as `hwConst q` by unfolding (compiles).
- Instances: `inst_svarF_pos_of_block_eq` proves "same block" by `fin_cases k <;> decide` on the three coordinates (no `decide` over `Idx`); `inst_kind_quad_tail_band` keeps `n`, `i` as variables; every bound is `1/2` (`inst_bounds`).
- No obstruction: no claim false, no negative statement compiled, no external hypothesis introduced (so no limit check is owed); only the sole writable file changed (`git diff --stat` above); `RBM3D/Test/Axioms.lean` untouched; the root import is the hub's.

## (c) Verified Mathlib names used (all `#check @name`, 0 errors; script `mathlib.lean`, 40 names)
MeasureTheory.Measure.infinitePi
MeasureTheory.Measure.infinitePi_map_pi
MeasureTheory.Measure.eq_infinitePi
MeasureTheory.Measure.infinitePi_pi
MeasureTheory.Measure.map_apply
MeasureTheory.Measure.map_map
ProbabilityTheory.gaussianReal
ProbabilityTheory.gaussianReal_map_const_mul
MeasureTheory.tendsto_measure_iUnion_atTop
measurableSet_lt
MeasureTheory.integral_mono
MeasureTheory.integrable_const
Matrix.IsHermitian.add
Matrix.IsHermitian.submatrix
Matrix.isHermitian_zero
Matrix.isHermitian_one
Continuous.matrix_submatrix
Continuous.matrix_elem
continuous_finsetSum
ZMod.val_natCast_of_lt
ZMod.val_lt
ZMod.val_injective
Nat.div_eq_of_lt
Nat.mul_div_cancel_left
exists_nat_one_div_lt
lt_div_iff₀
div_le_div₀
pow_le_one₀
pow_lt_pow_left₀
mul_self_lt_mul_self
one_div_le_one_div_of_le
Complex.mul_conj
Complex.normSq_eq_norm_sq
Complex.norm_conj
Complex.norm_real
Real.sq_sqrt
Real.sqrt_pos
Finset.single_le_sum
Finset.sum_mul_sum
Function.leftInverse_invFun
Names verified absent in RBM3D (`#check` error "unknown"): `RBM.Gauss.norm_green_le` (RBM2D Envelope; replaced by the private helper above), `RBM.Gauss.Xmat_apply` (private in FineModel), `RBM.Green.IBP_sum_svar_row` (RBM3D: `IBP_sum_svarF_row`).

## (d) Open issues and paper-delta candidates
- No open issue; no `sorry`; no registry edit (`TagFree` not flagged); instances nonempty and nondegenerate (`N = 216`, bounds `1/2`).
- `T2196a` (candidate): the quadratic LDE (4.7) holds for the minor of `A + X` with a deterministic Hermitian `A` (`gaussLaw_quad_tail`, `kind_quad_tail`); the RBM2D source (read) states the centred case only (`A = 0` is `gue_quad_tail`); RBM1D was not read. The paper (`3_5_Loop_Hierarchy.tex:13-38`, `lem_GbEXP`) cites Lemma 4.1 of [YY_25] and "large deviation estimates" and states no shifted form.
- `T2196b` (Lean structure, not a paper-statement delta): positivity of the auxiliary variance on one block comes from `sbKernelR d L g 0 = (1 + 2 d g²)⁻¹` for every `d`, `g` (RBM2D: `0 ∈ sbSupport 3`, `d = 2`); `auxSizes d` carries `lam ≡ 0`.
- `T2196c` (Lean parametrisation, not a paper-statement delta): `mixVar d L W g a b`, `Smix d L W g a b` carry the profile coupling `g` (RBM2D: the fixed band `gvar`), matching the merged `ouVar` (`rfl`).
