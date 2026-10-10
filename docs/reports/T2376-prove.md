Prover model: claude-sonnet-5-5
## (a) Math preflight — Sat Oct 10 09:10:46 UTC 2026

Read at worktree base 9d5d47d (main d38df76; `BA/KTreeRep.lean` last touched by ab54184 = K05b, 1763 lines). No Lean written, no `lake` run. Scripts (not in the repository): `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/966b45d4-be15-4db2-88b3-45a074bfecd5/scratchpad/T2376`: `k6.py` (mirrors of `KLFlong, KLTSPlong, KLwIn, KLshiftIn, KLFIn, KLcol, KLunCol, KLshiftOut, KLFOut, KLglueV, KLArcLe` `KLCut.lean:361-600, 914-960`, `sigmaIn, sigmaOut` `KLSumZeroWard.lean:70-77`; the cactus is T2374's `mirror.py`/`mgraph.py`, copied), `inst.py`, `gen.py`, `summ.py`, `table.py`. Notation: `J=(i,j)` a diagonal, `w=j-i`, `p=n-w+1` (outer polygon), `q=w+1` (inner), `Θ^{ss'}=BAThetaOf M t s s'=(1-tM^{(ss')})⁻¹`, `M_BA=BAMsigma d L (BAMB d L g (E:ℂ) m)`; `[NeZero L] [NeZero n]` throughout.

### (i) Statements (fixed here), exponent and constant table
| Lean name | statement (mathematics) | taken by |
|---|---|---|
| `BAKpi d L n M t σ a π` | `Σ_{F ∈ KLTSPlong n σ π} BAGamma d L n M t F σ a` (`(eq:defKpi)`, no `∏ m(σ_i)`) | K07, K08, K10 |
| `BASigmaTree d L M t F σ δ`, `BASigmaPi d L n M t σ π δ` | `KLgval δ (leaf weights 1) (BAslotLeaf F) (BACactusValEdgeW M t F σ) (BACactusValSrc F) (BACactusValTgt F) = Σ_{b: BAslot F→Zd} ∏_v 1[δ_v=b(leaf v)] ∏_{(i,j)∈F} (tΘ^{σ_iσ_j})(b(in J),b(out J)) ∏_s M(σ_{start(next s)})(b s,b(next s))`; `BASigmaPi := Σ_{F∈KLTSPlong n σ π} BASigmaTree` (`BAGamma` = same `KLgval` with leaf weights `Θ^{σ_vσ_{v+1}}`) | K07 (`(eq:molecule-decay)`, spanning tree), K08, K10 |
| `baK_eq_sum_Kpi` `(eq_K-Kpi)` | `0<κ, 0<g, 3≤L, BAReal d L g κ E m, 0≤t<1, 3≤n ⊢ BAKsol d L W M_BA (PropSpin m) t (KLloopOf d L σ a) = ((W:ℂ)^d)⁻¹^(n-1) · Σ_{π∈(diagonals n).powerset} BAKpi d L n M_BA t σ a π` | K07 (pure loop: only `π=∅`), K10 |
| `baKpi_eq_sum_SigmaPi` | `BAKpi d L n M t σ a π = Σ_{δ:Fin n→Zd d L} BASigmaPi d L n M t σ π δ · ∏_v Θ^{σ_vσ_{v+1}}(a_v,δ_v)`; no hypothesis | K08, K10 |
| `BAdeltaIn J δ u`, `BAdeltaOut J δ w` | `(δ_i..δ_{j-1}, u)` on `Fin(KLwIn J+1)`; `(δ_0..δ_{i-1}, w, δ_j..δ_{n-1})` on `Fin(n-KLwIn J+1)`, `w` at `KLglueV J` (= K05b `KTreeRep_aIn/aOut`, private there) | statement of the cut |
| `baCactus_cut` (public, generic; **proposed addition**, (iv)) | `KLIsTSP F, 2≤n, J∈F`, any `Lw:Fin n→Matrix`, any `P,S,Q`: `KLgval a Lw (BAslotLeaf F) (update (BACactusValEdgeW M t F σ) (inl J) (PSQ)) src tgt = Σ_{u,w} In(u) S_{uw} Out(w)`; `In(u)=KLgval (BAdeltaIn J a u) (update (Lw∘inVinv) last Pᵀ)` on `BAslot(KLFIn F J)`, edges `BACactusValEdgeW M t (KLFIn F J) (sigmaIn σ J)`; `Out(w)` likewise on `KLFOut F J`, `sigmaOut σ J`, `update (Lw∘outVinv) glue Q` | K10 (Θ-leaf cut), `baSigmaPi_cut` |
| `baSigmaPi_cut` (factorisation) | `2≤n, F₀∈TSP n, KLFlong F₀ σ=π, J∈π, ∀e∈π, KLArcLe e J→e=J ⊢ ∀δ, BASigmaPi d L n M t σ π δ = Σ_{u,w} BASigmaPi d L (KLwIn J+1) M t (sigmaIn σ J) ∅ (BAdeltaIn J δ u) · (tΘ^{σ_iσ_j})_{uw} · BASigmaPi d L (n-KLwIn J+1) M t (sigmaOut σ J) ((π.erase J).image (KLshiftOut J)) (BAdeltaOut J δ w)`; no `W`, no hypothesis on `M`,`t`; `u` (inner) is the row index | K08, K10 |
| `baSigmaPi_shift`, `baSigmaPi_reflect` | any `π`; `hshift: M σ(x+c)(y+c)=M σ x y` (reflect also `hsymm: M σ x y=M σ y x`) ⊢ `BASigmaPi…(δ+c)=BASigmaPi…δ`, `BASigmaPi…(c-δ)=BASigmaPi…δ` | K08 |
| `BASig d n L g E m t i σ δ`, `baSig_transl` | `BASigmaPi d (L i) n (BAMsigma (BAMB (L i) (g i) (E i) (m i))) (t i) σ ∅ δ`, `ι:Type, L:ι→ℕ, g E t:ι→ℝ, m:ι→ℂ`: has the type `∀ i,(Fin n→Bool)→(Fin n→Zd d (L i))→ℂ` of `Sig` (`SigSumZeroAbs` `KLIndStepA.lean:1036`, `IndStepAbs` `KLIndStepB.lean:77`); `baSig_transl` = the first two conjuncts, no hypothesis (`BAMsigma_shift` is **merged**, `KSolve.lean:558`; symmetry = copy of `BAMB_symm` `Ward.lean:83`) | K09b, K08b |

| quantity | value | constraint | slack |
|---|---|---|---|
| `n` | `≥3` (`baK_eq_sum_Kpi`: `BATreeRep`, `KTreeRep.lean:48`); `≥2` for the cut (`Flong_eq_iff_cut`, `KLsum_cut`) | `IsDiag`: `n≥4` for any cut | `n=3`: `diagonals 3=∅`, `K^{(∅)}=Γ_∅`; first cut `n=4` |
| width `w`, `p`, `q` | `2≤w≤n-2`, `p=n-w+1≥3`, `q=w+1≥3`, `p+q=n+2` | `KLdiag_width`; `table.py` below, `n=4..8` | `0` at `w=2` (`q=3`) and `w=n-2` (`p=3`) |
| `W` power | only `((W:ℂ)^d)⁻¹^(n-1)` in `baK_eq_sum_Kpi`; `BAKpi`, `BASigmaPi`, the cut, the clauses are `W`-free | K-level glue (K10): `(p-1)+(q-1)-1=n-1` | exact; no `W≠0` hypothesis (Lean `0⁻¹=0`) |
| `t` | `0≤t<1` only in `baK_eq_sum_Kpi` (via `baTreeRep`) | the other statements are algebraic (`PropThetaQ` is `Ring.inverse`): all real `t` | instance `t=1/2`; numerics `t∈{.55,.6,.7}` |
| `BAReal`, `κ`, `g`, `L` | `0<κ, 0<g` (`Λ:=g` in `baTreeRep`), `3≤L`, `BAReal d L g κ E m` | `BATreeRep` hypotheses verbatim | instance `(d,L)=(3,4)`, `κ=Im m=0.681`, `g=1/2` |
| layer / innermost | `π=KLFlong F₀ σ`, `J∈π`, no `e∈π∖{J}` inside the arc of `J` | `exists_innermost` (`KLSumZeroWard.lean:577`) gives `J` for every nonempty `π⊆diagonals n` (`Flong_subset_diagonals` `:594`) | `n=5`, `π={(0,3),(1,3)}`: `J=(1,3)` innermost, `(0,3)` not (control fails by 0.67) |
| orientation (C2) | chord weight `tΘ^{σ_iσ_j}`, inner end `u` first; reversed inner leaf `Θ^{σ_jσ_i}=(Θ^{σ_iσ_j})ᵀ` holds for every `M` | Σ-level leaves are indicators, `1ᵀ=1`: **no symmetry of `M` used**; the reflection clause uses `M(σ)ᵀ=M(σ)` (`BAMB_symm`, merged, unconditional) | non-symmetric data passes (1e-17); transposed chord fails (1e-3): the test sees orientation |
| tolerance | ticket `≤1e-12`, no ODE | max abs error `6.84e-14` (values up to `16`); instance: abs `≤4.7e-19` at values `1e-8..2e-4` (relative `≤6e-14`) | `14.6×` |
| size | central `1500`, low `1300`, high `1800` ((iv)) | stop line `1500` (binding) | `0 / 200 / -300` |

### (ii) One concrete nondegenerate instance, and the binding numerics
**Hypotheses of the targets.** `baK_eq_sum_Kpi`: `0<κ`, `0<g`, `3≤L`, `BAReal`, `0≤t<1`, `3≤n`; cut: `J` innermost in a nonempty layer; clauses: none. No external hypothesis: `baTreeRep` is merged (K05b); the third conjunct of `SigSumZeroAbs` (K07/K08) stays a hypothesis of the interface `example` (another gate's pin), so no limit computation is owed. Lean instance (1b): flow point `P` of `(d,L)=(3,4)` (`MFixedPoint.lean:893`, `P.real:BAReal 3 4 P.g0 P.m0.im P.E P.m0`), `W=2`, `t=1/2`, `n=4`, `σ=(+,+,-,+)`, `J=(0,2)`, `π={(0,2)}`, four distinct labels as in K05b's instances; `P` is a choice, so the script uses `g=1/2, E=0.3` and `m` solving `BASelf` (same `BAReal` shape). `cd $S; python3 inst.py`:
```
N=L^d=64, 3<=L True, 0<g=0.5<=Lambda=10 True, W^d=8, t=0.5 in [0,1) True; m=-0.096078036+0.681402583j, BASelf residual 2.3e-16, kappa=Im m=0.681403>0 True; M symmetric True, M(x+r,y+r)=M(x,y) 1.0e-15
n=4, sigma=++-+, J=(0, 2) (IsDiag True, sigma_i!=sigma_j True), |TSP n|=3, layer sizes {[]: 2, [(0, 2)]: 1}
  layer pi=[(0, 2)] (1 trees), J innermost: True, (outer,inner) lengths (3,3), pi'=[]; delta=(30, 16, 47, 60): Sigma_pi=-1.77759e-07+1.14881e-07j, factorisation=-1.77759e-07+1.14881e-07j; 12 random delta: max diff 9.6e-21, both sides nonzero 12/12
n=4, sigma=+---, J=(0, 2) (IsDiag True, sigma_i!=sigma_j True), |TSP n|=3, layer sizes {[]: 2, [(0, 2)]: 1}
  layer pi=[(0, 2)] (1 trees), J innermost: True, (outer,inner) lengths (3,3), pi'=[]; delta=(41, 13, 27, 34): Sigma_pi=-1.49744e-07+4.68143e-08j, factorisation=-1.49744e-07+4.68143e-08j; 12 random delta: max diff 1.3e-21, both sides nonzero 12/12
(eq_K-Kpi) n=4, sigma=++-+, a=(30, 38, 55, 33), W=2: sum_F Gamma_F=-2.37133e-05-1.03768e-05j; sum_pi Kpi=-2.37133e-05-1.03768e-05j; diff 1.7e-21; Kpi by pi (#trees): (): -2.205e-05-1.057e-05j (2); ((0, 2),): -1.661e-06+1.947e-07j (1); ((1, 3),): 0.000e+00 (0); ((0, 2), (1, 3)): 0.000e+00 (0); W^-d(n-1) sum = -4.63150e-08-2.02673e-08j
first stage, pi={(0,2)}: Kpi(a)=-1.66060e-06+1.94688e-07j; sum_delta Sigma_pi(delta) prod_v Theta(a_v,delta_v)=-1.66060e-06+1.94688e-07j (sum over 64^4 = 16777216 delta); diff 8.1e-21
clauses, alternating sigma=+-+-, layer pi={} has 3 trees (= |TSP 4|: True):
  c=(2, 2, 0), delta=(38, 43, 1, 53): Sigma(delta)=1.63627e-04+6.03531e-05j, Sigma(delta+c)=1.63627e-04+6.03531e-05j, Sigma(c-delta)=1.63627e-04+6.03531e-05j; 10 random (c,delta): max|Sigma(delta+c)-Sigma(delta)|=3.0e-19, max|Sigma(c-delta)-Sigma(delta)|=4.7e-19, Sigma nonzero 10/10
n=5, sigma=+++--, J=(1, 3) (IsDiag True, sigma_i!=sigma_j True), |TSP n|=11, layer sizes {[]: 2, [(0, 3)]: 2, [(0, 3), (1, 3)]: 1, [(1, 3)]: 1, [(1, 3), (1, 4)]: 1, [(1, 4)]: 1, [(1, 4), (2, 4)]: 1, [(2, 4)]: 2}
  layer pi=[(0, 3), (1, 3)] (1 trees), J innermost: True, (outer,inner) lengths (4,3), pi'=[(0, 2)]; delta=(27, 57, 34, 28, 15): Sigma_pi=2.32735e-08-7.60213e-08j, factorisation=2.32735e-08-7.60213e-08j; 6 random delta: max diff 1.2e-21, both sides nonzero 6/6
  layer pi=[(1, 3)] (1 trees), J innermost: True, (outer,inner) lengths (4,3), pi'=[]; delta=(28, 4, 58, 36, 43): Sigma_pi=4.70168e-08-3.24272e-08j, factorisation=4.70168e-08-3.24272e-08j; 6 random delta: max diff 2.6e-22, both sides nonzero 6/6
  layer pi=[(1, 3), (1, 4)] (1 trees), J innermost: True, (outer,inner) lengths (4,3), pi'=[(1, 3)]; delta=(45, 28, 25, 15, 15): Sigma_pi=-3.67445e-07+4.31610e-07j, factorisation=-3.67445e-07+4.31610e-07j; 6 random delta: max diff 2.7e-22, both sides nonzero 6/6
```
**Binding numerics (no ODE).** `python3 k6.py layers 6 > layers_out.txt; python3 summ.py layers_out.txt` (115 s). Data: BA-A `q=4,g=.5,E=.3,t=.7`; BA-B `q=3,g=1.1,E=0,t=.6` (cycle `Z_q`, `M(-)=Mᴴ`, symmetric); RAND `q=3`, `M(+),M(-)` independent random non-symmetric, `t=.55`. Every `σ`, every `π`, **every** `δ` and `a` (full arrays, no sampling). (A) `(eq_K-Kpi)`: `Σ_{F∈TSP n}Γ_F` vs `Σ_{π⊆diagonals n}BAKpi`; (B) `BAKpi` vs `Σ_δ BASigmaPi ∏Θ`; (C) the factorisation for every innermost `J∈π` of every nonempty layer, with `FOut,FIn,sigmaOut,sigmaIn,shiftOut,BAdeltaIn/Out` mirrored from the Lean text; "layer-iff-cut" = `KLFlong F σ=π ⇔ (KLFlong (KLFOut F J)=π' ∧ KLFlong (KLFIn F J)=∅)` for every `F∈TSP n`, `J∈F`, and `FOut∈TSP p`, `FIn∈TSP q`; controls: `J∈π` not innermost, and the transposed chord `(tΘ)ᵀ`.
```
data  n  |TSP| (A)err/max  (B)err/max  (C)#cases err (max|Sigma|) layer-iff-cut,partition | control non-innermost J: #,max diff | control transposed chord: #,max diff
BA-A  3    1   0.00e+00/2.1e+00  1.78e-15/2.1e+00    0 0.00e+00 (0.0e+00)  True,True |   0, 0.00e+00 |   0, 0.00e+00
BA-A  4    3   4.44e-16/4.4e+00  6.22e-15/4.4e+00   16 3.33e-16 (6.4e-01)  True,True |   0, 0.00e+00 |  16, 1.67e-16
BA-A  5   11   5.33e-15/7.0e+00  8.45e-15/3.1e+00  128 3.34e-16 (6.7e-01)  True,True |  32, 6.72e-01 | 128, 4.45e-16
BA-A  6   45   3.91e-14/1.6e+01  6.84e-14/6.5e+00  832 5.56e-16 (7.1e-01)  True,True | 416, 7.13e-01 | 832, 5.80e-16
BA-B  3    1   0.00e+00/1.5e+00  6.68e-16/1.5e+00    0 0.00e+00 (0.0e+00)  True,True |   0, 0.00e+00 |   0, 0.00e+00
BA-B  4    3   2.22e-16/3.0e+00  1.78e-15/3.0e+00   16 1.12e-16 (2.9e-01)  True,True |   0, 0.00e+00 |  16, 1.11e-16
BA-B  5   11   3.55e-15/5.1e+00  2.26e-15/1.8e+00  128 8.33e-17 (2.1e-01)  True,True |  32, 1.95e-01 | 128, 7.85e-17
BA-B  6   45   1.52e-14/1.1e+01  1.03e-14/3.7e+00  832 8.58e-17 (1.6e-01)  True,True | 416, 1.59e-01 | 832, 8.78e-17
RAND  3    1   0.00e+00/1.1e+00  1.14e-16/1.1e+00    0 0.00e+00 (0.0e+00)  True,True |   0, 0.00e+00 |   0, 0.00e+00
RAND  4    3   5.72e-17/2.0e+00  5.55e-16/2.0e+00   16 5.82e-18 (1.3e-02)  True,True |   0, 0.00e+00 |  16, 9.73e-04
RAND  5   11   1.24e-16/4.2e+00  1.83e-15/4.2e+00  128 5.49e-18 (1.4e-02)  True,True |  32, 1.38e-03 | 128, 1.05e-03
RAND  6   45   4.58e-16/9.8e+00  5.62e-15/9.8e+00  832 1.04e-17 (2.1e-02)  True,True | 416, 1.48e-03 | 832, 1.48e-03
```
```
BA-sym   n=4: #(sigma,pi)=32: max|Sigma(delta+c)-Sigma(delta)|=1.49e-15; max|Sigma(c-delta)-Sigma(delta)|=1.49e-15
BA-sym   n=6: #(sigma,pi)=784: max|Sigma(delta+c)-Sigma(delta)|=3.82e-15; max|Sigma(c-delta)-Sigma(delta)|=3.82e-15
CONTROL circulant NON-symmetric M(+),M(-) n=4: #(sigma,pi)=32: max|Sigma(delta+c)-Sigma(delta)|=1.43e-17; max|Sigma(c-delta)-Sigma(delta)|=1.11e-01
CONTROL circulant NON-symmetric M(+),M(-) n=6: #(sigma,pi)=784: max|Sigma(delta+c)-Sigma(delta)|=1.43e-17; max|Sigma(c-delta)-Sigma(delta)|=4.91e-02
n, |TSP n|, #diagonals, min(p,q), all-J check (2<=w<=n-2, p,q>=3, p+q=n+2, (FOut,FIn): {F in TSP n: J in F} -> TSP p x TSP q bijective): [(4, 3, 2, 3, True), (5, 11, 5, 3, True), (6, 45, 9, 3, True), (7, 197, 14, 3, True), (8, 903, 20, 3, True)]
generic cut, n=4..6, every diagonal J, 3 random sigma each, random Lw,P,S,Q, all F in TSP n with J in F: 330 cases, max|LHS - RHS| = 1.43e-14 (max|LHS| = 4.0e+01)
```
Commands for the last block: `python3 k6.py clauses | head -4` (translation and reflection of `Σ^{(π)}` on `Z_4`, every `σ` and `π`; control: shift-invariant non-symmetric `M`), `python3 table.py` (cut sizes), `python3 gen.py` (generic cut at random non-symmetric data). No indexing failure, no false identity: no pin repair, no REQ.

### (iii) The written argument
**First stage and (eq_K-Kpi).** `BAGamma` and `BASigmaTree` are `KLgval` on the slots with the same edges and leaf weights `Θ_v` resp. `1`. Generic: `KLgval a Lw p E c q = Σ_δ KLgval δ 1 p E c q · ∏_ℓ Lw ℓ (a ℓ)(δ ℓ)` (expand `∏_ℓ Lw_ℓ(a_ℓ,b(pℓ)) = Σ_δ ∏_ℓ 1[δ_ℓ=b(pℓ)] Lw_ℓ(a_ℓ,δ_ℓ)` by `Finset.prod_univ_sum`, swap sums; twin of `KLtreeValW_eq_sum_selfW`, `KLTree.lean`); summing over `KLTSPlong n σ π` is `baKpi_eq_sum_SigmaPi`. `baK_eq_sum_Kpi`: `baTreeRep d` at `Λ:=g` gives `BAKsol = (W^d)⁻¹^(n-1) Σ_{F∈TSP n}Γ_F`; the fibres of `F↦KLFlong F σ` lie in `(diagonals n).powerset` (`KLFlong F σ⊆F⊆diagonals n`), so `Σ_{F∈TSP n}=Σ_π Σ_{F∈KLTSPlong n σ π}` (copy of the private `KLsum_TSPlong`, `KLTree.lean:381`).
**Cut of one tree (`baCactus_cut`).** `KLgval_split` (`KLCut.lean:116`) with `N₁=BAslot(F_out)`, `N₂=BAslot(F_in)`, `c₀=` leaf slot `last` of `F_in`, `q₀=` leaf slot `glue` of `F_out`, edge weight `P·S·Q`: `Σ_{u,w} part₂(u) S_{uw} part₁(w)`, new leaves `(u,Pᵀ)` on `c₀` and `(w,Q)` on `q₀`. The slot relabelling `BAslot F_out ⊕ BAslot F_in ≃ BAslot F` (leaves: `KLoutV/KLinV` inverses, `leaf(glue)↦out J`, `leaf(last)↦in J`; chords: `KLunColP`, `KLunShift`) commutes with `BAnextSlot` and `BAslotStart`, hence with `BAMcharge`; chord ends keep their charges (`sigmaOut_shiftOut`, `sigmaIn_shiftIn`); `KLgval_congr` transports. This is K05b's `KTreeRep_cut` (`KTreeRep.lean:1284`, private, with `Lw=Θ`, `P=Q=Θ`, `S=1`), whose helpers for maps, slot relabellings and charges (`:74-146`, `:262-1136`; no leaf weight occurs in them) are copied with the stem `KMolecule_`; only `CutParts`/`CutThm` (`:1138-1368`) change (leaf weights are `Lw`, `Pᵀ`, `Q` as given; no `KTreeRep_Theta_swap`). `gen.py` checks the generic statement at random non-symmetric data.
**Layer bijection and gluing (`baSigmaPi_cut`).** `J∈π⊆F` for `F∈KLTSPlong n σ π` (`Flong_subset`); for `F∈TSP n`, `J∈F`: `KLFlong F σ=π ⇔ KLFlong F_out=(π∖J)'∧KLFlong F_in=∅` (`Flong_eq_iff_cut`, `KLSumZeroWard.lean:165`, `hinner`). So `KLTSPlong n σ π={F∈TSP n: J∈F}∩{layer cond}` and `Σ_F BASigmaTree` is, by `baCactus_cut` at `Lw=1`, `P=Q=1` (`1ᵀ=1`), `S=tΘ^{σ_iσ_j}`, a function of `(F_out,F_in)`; `KLsum_cut` (`KLCut.lean:1297`) turns `Σ_{F∈TSP n, J∈F}` into `Σ_{G∈TSP p}Σ_{H∈TSP q}`, the conditions into `G∈KLTSPlong p σ_out π'`, `H∈KLTSPlong q σ_in ∅`, and the sum factorises: `Σ_{u,w} Σ_H In · S_{uw} · Σ_G Out` (as `Qlayer_cut`, `KLSumZeroWard.lean:293`, for the scalar `Q`). **W-free:** `BASigmaTree` has no `W`; the `W` of `K` sits in `baK_eq_sum_Kpi` only (`n-1=(p-1)+(q-1)-1` is K10's K-level count). **Reversed leaf (C2):** `KLgval_split` puts `Pᵀ` on the inner new leaf; at the Σ level it is `1`, so the orientation is only the convention `u`=inner end (row index of `S`), checked by the transposed control; the K-level reversal `Θ^{σ_jσ_i}=(Θ^{σ_iσ_j})ᵀ` (general `M`: `BAMssOf M s' s=(BAMssOf M s s')ᵀ`) is K10's and needs no symmetry. **Leaf removal:** the indicator `1[δ_v=b(leaf v)]` of the pieces is `1(a_k,·)` with `a_k=BAdeltaIn/Out`; the new leaves carry `1[u=b(c₀)]`, `1[w=b(q₀)]`.
**Clauses.** `M(σ)(c-x,c-y)=M(σ)(x,y)`: shift by `x+y-c` (`BAMsigma_shift`), then symmetry; the same for `M^{(σσ')}`; `Θ=Ring.inverse(1-tM^{(σσ')})` is invariant under conjugation by the permutations `x↦x+c`, `x↦c-x` (`Matrix.inv_submatrix_equiv`, as `BAMB_shift`, `Ward.lean:53`), no invertibility. `BASigmaTree` is a sum over `b`; substituting `b=b'+c` resp. `b=c-b'` (`Equiv.sum_comp`) turns `1[δ_v+c=b(leaf v)]` resp. `1[c-δ_v=b(leaf v)]` into `1[δ_v=b'(leaf v)]` and fixes every edge weight: `Σ(δ+c)=Σ(δ)`, `Σ(c-δ)=Σ(δ)`, every `σ` and `π`. Ticket text: the first conjunct is a point reflection (needs `BAMB_symm`, allowed by C2), not a translation; "`BAMsigma_shift`" is already merged (M-level), the `Θ`-level invariance is the new private lemma.

### (iv) Plan against the stop line `1500` (`wc -l RBM3D/BA/KMolecule.lean` at each commit; counts are K05b sections stripped of docstrings and blanks: Maps 49, Transport 28, InSide 71, InSlots 151, OutSide 123, OutSlots 146, CutEquivs 73, CutEquivs2 69, CutLabels 62, CutMain 18, CutParts 121, CutThm 87 = 998 of 1160 raw)
| § | content | central / cumulative |
|---|---|---|
| 0-1 | header, imports, defs `BAKpi, BASigmaTree, BASigmaPi, BAdeltaIn/Out, BASig` | 105 / 105 |
| 2 | generic first-stage lemma, `baKpi_eq_sum_SigmaPi`, `KLsum_TSPlong` copy, `baK_eq_sum_Kpi` | 75 / 180 (commit 1) |
| 3 | `Θ`-level shift/reflect, `M` symmetric copy, label-bijection lemma, `baSigmaPi_shift/reflect`, `baSig_transl` | 120 / 300 (commit 2) |
| 4 | copy of K05b §1-§5 (maps, `φ`,`ψ`, next/start/charge compatibility), without the cutGlue list lemmas (`:148-260`) | 650 / 950 (commits 3-4) |
| 5 | `baCactus_cut` (generic leaf weights; K05b CutParts+CutThm adapted) | 200 / 1150 (commit 5) |
| 6 | layer assembly, `KLsum_cut`, `baSigmaPi_cut` | 110 / 1260 |
| 7 | instances (5 `example`s at `P`, `n=4`, `J=(0,2)`; interface `example` with the third conjunct as hypothesis) | 90 / 1350; public docstrings `+100` = `1450-1500` |
**The stop line binds at the central estimate** (K05b: 1763 against a preflight 1300). The cost is the copied cut machinery (§4-§5, about 850 lines), which cannot be shortened inside one file. Decision points: after §5 if `wc -l > 1250`, §6-7 (about 200) will not fit. Options for the dispatcher (not decided here): (a) raise the stop line to 1800; (b) allow a second file for §4-§5 (then only `KMolecule.lean` is imported by K07/K08/K10). Public `baCactus_cut` lets K10 (cut at an innermost long edge) import the cut instead of copying the same private helpers a second time; if the 1a-audit refuses it, it becomes `private` and no other statement changes.

### Verdicts
Reasons: every hypothesis set is satisfiable at once (the instance of (ii): `BAReal` at `κ=0.681`, `0<g≤Λ`, `3≤L`, `t=1/2`, `n=4,5`, nonempty layers, `J` innermost, both sides of every identity nonzero); the exponent rows close exactly (`p+q=n+2`, `p,q≥3`); every identity of (ii) holds to `≤7e-14` on all `σ`, `π`, `δ`, `a` at `n=3..6`, with controls (non-innermost `J`, transposed chord, non-symmetric reflection) failing at `1e-3..7e-1`. Ticket-text findings (no verdict changes): `BAMsigma_shift` is merged (`KSolve.lean:558`), only the `Θ`-level invariance and `M` symmetry are new; the first conjunct of `SigSumZeroAbs` is a reflection; `KLsum_TSPlong` is at `KLTree.lean:381` (ticket `:384`); C2 is not binding at the Σ level.
`BAKpi`/`BASigmaPi`/`BASigmaTree`: PASS. `baK_eq_sum_Kpi`: PASS. `baKpi_eq_sum_SigmaPi`: PASS. `baCactus_cut` (proposed): PASS. `baSigmaPi_cut`: PASS (C2 route needs no non-symmetric-`M` fact). `BASig`, `baSig_transl`, `baSigmaPi_shift/reflect`: PASS. Instances: PASS (nonvacuous data above). Registry: none expected. Paper-delta candidates: `T2376a` BA chord `tΘ^{(σ_i,σ_j)}` for both orientations against the paper's `tS^{(B)}Θ^{(+,-)}` in `(eq:molecule-Kpi)` (`S^{(B)}=I`; equal by `BATheta_swap`); `T2376b` the BA `Σ^{(π)}`, `K^{(π)}` carry no `∏m(σ_i)` (as `BATreeRep`). **Overall: PASS; open: the stop-line decision of (iv).**

## (b) Stage 1b — Amend 1 (`docs/tickets/T2376-amend-1.md`; role prover-max; two files; combined stop line 2000)
Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2376`, branch `t/T2376` at 9d5d47d. Scratch: `scratchpad/T2376/1b/`.

### (b1) Plan (iv) restated under Amend 1 — Sat Oct 10 09:40 UTC 2026 (written before any Lean)
Measured K05b copy sizes (`python3 count.py RBM3D/BA/KTreeRep.lean`, raw / code lines): Maps 71/49, Transport 36/28, InSide 84/71, InSlots 175/151, OutSide 141/123, OutSlots 170/146, CutEquivs 87/73, CutEquivs2 80/69, CutLabels 70/62, CutMain 24/18: **938 raw / 790 code** are copied with the stem `KCactusCut_`; CutParts + CutThm (230 raw / 208 code) are rewritten for generic leaf weights. **Dropped K05b lemmas:** the `Lists` section (113 raw: `KTreeRep_cutGlueL_eq`, `KTreeRep_cutGlueR_eq`, list identities used only by `baChordPairs`); the four defs `KTreeRep_σIn/σOut/aIn/aOut` (replaced by merged `sigmaIn`, `sigmaOut` (`KLSumZeroWard.lean:70,75`) and the public `BAdeltaIn/BAdeltaOut`); `KTreeRep_in_part/out_part/cut` (replaced by the generic `baCactus_cut`).
| step | file | content | raw lines (est.) | cumulative, both files |
|---|---|---|---|---|
| C0 | KCactusCut | header; public `BAinVinv`, `BAoutVinv`, `BAdeltaIn`, `BAdeltaOut`; 6 vertex-map lemmas | 75 | 75 |
| C1 | KCactusCut | copy Transport, InSide, InSlots (`KTreeRep.lean:262-558`) | 297 | 372 (commit) |
| C2 | KCactusCut | copy OutSide, OutSlots (`:560-871`) | 312 | 684 (commit) |
| C3 | KCactusCut | copy CutEquivs, CutEquivs2, CutLabels, CutMain (`:873-1136`) | 264 | 948 (commit) |
| C4 | KCactusCut | generic `baCactus_cut`, chord-charge and label lemmas; public Θ-leaf identities for K10 | 190 | 1140 (commit) |
| M1 | KMolecule | header; `BAKpi`, `BASigmaTree`, `BASigmaPi`, `BASig`; generic first-stage lemma; `baKpi_eq_sum_SigmaPi`; `baK_eq_sum_Kpi` | 170 | 1310 (commit) |
| M2 | KMolecule | invariance of `Θ` and of the tree value under a label permutation; `baSigmaPi_shift/reflect`; `baSig_transl` | 110 | 1420 (commit) |
| M3 | KMolecule | layer assembly with `KLsum_cut`, `baSigmaPi_cut` | 110 | 1530 (commit) |
| M4 | KMolecule | instances (5 `example`s at the flow point `P` of `(3,4)`, `n=4`), interface `example` | 90 | 1620 (commit) |
Decision points (all against 2000): after C4, `wc -l KCactusCut.lean` must be ≤ 1350, else drop the Θ-leaf lemmas (about 70 lines) and the private docstrings, and if still above stop and RETURN; after M2 the sum must be ≤ 1800 (M3 + M4 ≈ 200); the sum is checked with `wc -l` of both files at every commit. Central estimate 1620 (high 1800), under 2000.

### (b2) Script output (scripts in `scratchpad/T2376/1b/`, rerun by `mk_final.sh`) — Sat Oct 10 10:15:00 UTC 2026
```
$ git diff --stat main...t/T2376
 RBM3D/BA/KCactusCut.lean | 1288 ++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/BA/KMolecule.lean  |  449 ++++++++++++++++
 2 files changed, 1737 insertions(+)
$ lake build RBM3D.BA.KCactusCut RBM3D.BA.KMolecule 2>&1 | tail -1
Build completed successfully (3752 jobs).
$ lake env lean RBM3D/BA/KCactusCut.lean; echo exit=$?; lake env lean RBM3D/BA/KMolecule.lean; echo exit=$?   # no diagnostics printed
exit=0
exit=0
$ lake env lean docs/tickets/checks/T2376-check.lean > /dev/null 2>&1; echo exit=$?
exit=0
$ grep -c 'sorry\|admit\|native_decide\|^axiom' RBM3D/BA/KMolecule.lean RBM3D/BA/KCactusCut.lean
RBM3D/BA/KMolecule.lean:0
RBM3D/BA/KCactusCut.lean:0
$ lake env lean axioms.lean   # #print axioms of the 17 public declarations, grouped by python3 axgroup.py
exit=0
[propext, Quot.sound]: 4 declarations: BAinVinv, BAoutVinv, BAdeltaIn, BAdeltaOut
[propext, Classical.choice, Quot.sound]: 13 declarations: baCactus_cut, baCactus_leafW_in, baCactus_leafW_out, BAKpi, BASigmaTree, BASigmaPi, BASig, baK_eq_sum_Kpi, baKpi_eq_sum_SigmaPi, baSigmaPi_shift, baSigmaPi_reflect, baSigmaPi_cut, baSig_transl
$ combined wc -l at each section commit (git show <commit>:<file> | wc -l, UTC commit times); stop line 2000
9938bd8 09:44:29 UTC KMolecule=0 KCactusCut=1194 combined=1194  KCactusCut sections C0-C4 (copied cut machinery 
45fe7da 09:47:45 UTC KMolecule=155 KCactusCut=1194 combined=1349  KMolecule section M1 (BAKpi, BASigmaTree, BASigm
d6d30df 09:48:53 UTC KMolecule=263 KCactusCut=1194 combined=1457  KMolecule section M2 (shift and reflection claus
5252f53 09:50:28 UTC KMolecule=378 KCactusCut=1194 combined=1572  KMolecule section M3 (layer assembly, baSigmaPi_
040d455 09:53:11 UTC KMolecule=454 KCactusCut=1287 combined=1741  KMolecule section M4 (instances), KCactusCut lea
ab616f0 10:00:28 UTC KMolecule=445 KCactusCut=1288 combined=1733  final polish (explicit d L in BASigmaTree, docst
3fa3746 10:12:30 UTC KMolecule=449 KCactusCut=1288 combined=1737  IndStepAbs type-match example for BASig
$ python3 secsizes.py   # lines per `## N.` section of each file
KCactusCut.lean: header 35, §1 68, §2 37, §3 261, §4 313, §5 267, §6 117, §7 96, §8 59, §9 35  (total 1288)
KMolecule.lean: header 48, §1 29, §2 67, §3 109, §4 115, §5 81  (total 449)
$ git log -1 --format=%h -- RBM3D/BA/KTreeRep.lean   # source of the copied text (no RBM1D/RBM2D port: nothing read there)
ab54184
$ name clash: grep -rnw <name> RBM3D RBM3D.lean (branch, outside the two files) + main worktree; 17 public names, stems KMolecule_, KCactusCut_
total hits over the 19 patterns, branch + main (main at 1f710ee): 0
$ registry pre-check, temporary uncommitted file (scratchpad), its lines joined by ;
import RBM3D;import RBM3D.BA.KCactusCut;import RBM3D.BA.KMolecule;#assert_rbm_axioms;
$ lake env lean precheck.lean > precheck_out.txt; echo exit=$?; head -1 precheck_out.txt; wc -l < precheck_out.txt
exit=0
axiom audit: 10951 theorems, 3220 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
     253
$ same file without the two new imports: exit, first line; diff of the premise ledgers (lines 2-end)
exit=0
axiom audit: 10937 theorems, 3212 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
ledger lists identical (diff exit 0)
$ lake env lean k10check.lean; echo exit=$?   # scratch (not committed): K05b KTreeRep_cut from baCactus_cut + baCactus_leafW_in/out
exit=0
```
Target statements, extracted from the files by `python3 stmts.py` (the 1a table rows are the pins; the definitions are shown with their bodies):
```
--- RBM3D/BA/KCactusCut.lean
L44: def BAinVinv (J : Fin n × Fin n) (k : Fin (KLwIn J + 1)) : Fin n := ⟨min (J.1.val + k.val) (n - 1), by have := NeZero.pos n; omega⟩
L49: def BAoutVinv (J : Fin n × Fin n) (k : Fin (n - KLwIn J + 1)) : Fin n := ⟨min (KLunCol J k.val) (n - 1), by have := NeZero.pos n; omega⟩
L54: def BAdeltaIn {α : Type*} (J : Fin n × Fin n) (f : Fin n → α) (x : α) : Fin (KLwIn J + 1) → α := Function.update (fun k => f (BAinVinv J k)) (Fin.last _) x
L59: def BAdeltaOut {α : Type*} (J : Fin n × Fin n) (f : Fin n → α) (x : α) : Fin (n - KLwIn J + 1) → α := Function.update (fun k => f (BAoutVinv J k)) (KLglueV J) x
L1111: theorem baCactus_cut (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin n → Bool) (a : Fin n → Zd d L) (Lw : Fin n → Matrix (Zd d L) (Zd d L) ℂ) (P S Q : Matrix (Zd d
    L) (Zd d L) ℂ) : KLgval d L (Nd := BAslot F) (Lf := Fin n) a Lw (BAslotLeaf F) (Function.update (BACactusValEdgeW M t F σ) (Sum.inl ⟨J, hJ⟩) (P * S * Q)) (BACactusValSrc F) (BACactusValTgt F) = ∑ u : Zd d L, ∑ w
    : Zd d L, KLgval d L (Nd := BAslot (KLFIn F J)) (Lf := Fin (KLwIn J + 1)) (BAdeltaIn J a u) (BAdeltaIn J Lw Pᵀ) (BAslotLeaf (KLFIn F J)) (BACactusValEdgeW M t (KLFIn F J) (sigmaIn σ J)) (BACactusValSrc (KLFIn F
    J)) (BACactusValTgt (KLFIn F J)) * S u w * KLgval d L (Nd := BAslot (KLFOut F J)) (Lf := Fin (n - KLwIn J + 1)) (BAdeltaOut J a w) (BAdeltaOut J Lw Q) (BAslotLeaf (KLFOut F J)) (BACactusValEdgeW M t (KLFOut F J)
    (sigmaOut σ J)) (BACactusValSrc (KLFOut F J)) (BACactusValTgt (KLFOut F J)) := by
L1204: theorem baCactus_leafW_in (hJ : J.1.val + 2 ≤ J.2.val) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin n → Bool) : BAdeltaIn J (BACactusValLeafW M t σ) (BAThetaOf M t (σ J.1) (σ J.2))ᵀ = BACactusValLeafW M
    t (sigmaIn σ J) := by
L1232: theorem baCactus_leafW_out (hJ : J.1.val + 2 ≤ J.2.val) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin n → Bool) : BAdeltaOut J (BACactusValLeafW M t σ) (BAThetaOf M t (σ J.1) (σ J.2)) = BACactusValLeafW M
    t (sigmaOut σ J) := by
--- RBM3D/BA/KMolecule.lean
L53: noncomputable def BAKpi (d L n : ℕ) [NeZero L] [NeZero n] (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin n → Bool) (a : Fin n → Zd d L) (π : Finset (Fin n × Fin n)) : ℂ := ∑ F ∈ KLTSPlong n σ π, BAGamma d
    L n M t F σ a
L60: noncomputable def BASigmaTree (d L : ℕ) [NeZero L] {n : ℕ} [NeZero n] (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (F : Finset (Fin n × Fin n)) (σ : Fin n → Bool) (δ : Fin n → Zd d L) : ℂ := KLgval d L (Nd :=
    BAslot F) (Lf := Fin n) δ (fun _ => 1) (BAslotLeaf F) (BACactusValEdgeW M t F σ) (BACactusValSrc F) (BACactusValTgt F)
L67: noncomputable def BASigmaPi (d L n : ℕ) [NeZero L] [NeZero n] (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n)) (δ : Fin n → Zd d L) : ℂ := ∑ F ∈ KLTSPlong n σ π,
    BASigmaTree d L M t F σ δ
L74: noncomputable def BASig {ι : Type} (d n : ℕ) [NeZero n] (L : ι → ℕ) [∀ i, NeZero (L i)] (g E : ι → ℝ) (m : ι → ℂ) (t : ι → ℝ) (i : ι) (σ : Fin n → Bool) (δ : Fin n → Zd d (L i)) : ℂ := BASigmaPi d (L i) n (BAMsigma
    d (L i) (BAMB d (L i) (g i) ((E i : ℝ) : ℂ) (m i))) (t i) σ ∅ δ
L110: theorem baKpi_eq_sum_SigmaPi (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin n → Bool) (a : Fin n → Zd d L) (π : Finset (Fin n × Fin n)) : BAKpi d L n M t σ a π = ∑ δ : Fin n → Zd d L, BASigmaPi d L n M t σ
    π δ * ∏ v, BAThetaOf M t (σ v) (σ (v + 1)) (a v) (δ v) := by
L133: theorem baK_eq_sum_Kpi (d : ℕ) {κ g : ℝ} (hκ : 0 < κ) (hg : 0 < g) {L : ℕ} [NeZero L] (hL : 3 ≤ L) (W : ℕ) {E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) {n : ℕ} [NeZero n] (hn : 3 ≤
    n) (σ : Fin n → Bool) (a : Fin n → Zd d L) : BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t (KLloopOf d L σ a) = (((W : ℂ) ^ d)⁻¹) ^ (n - 1) * ∑ π ∈ (diagonals n).powerset, BAKpi d L n
    (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ a π := by
L204: theorem baSigmaPi_shift (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (hshift : ∀ (σ : Bool) (x y c : Zd d L), M σ (x + c) (y + c) = M σ x y) (t : ℝ) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n)) (δ : Fin n → Zd d L) (c
    : Zd d L) : BASigmaPi d L n M t σ π (fun j => δ j + c) = BASigmaPi d L n M t σ π δ :=
L224: theorem baSigmaPi_reflect (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (hshift : ∀ (σ : Bool) (x y c : Zd d L), M σ (x + c) (y + c) = M σ x y) (hsymm : ∀ (σ : Bool) (x y : Zd d L), M σ x y = M σ y x) (t : ℝ) (σ : Fin n →
    Bool) (π : Finset (Fin n × Fin n)) (δ : Fin n → Zd d L) (c : Zd d L) : BASigmaPi d L n M t σ π (fun j => c - δ j) = BASigmaPi d L n M t σ π δ :=
L313: theorem baSigmaPi_cut (hn : 2 ≤ n) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin n → Bool) {F₀ : Finset (Fin n × Fin n)} (hF₀ : F₀ ∈ TSP n) {π : Finset (Fin n × Fin n)} (hπ : KLFlong F₀ σ = π) (hJπ : J ∈
    π) (hinner : ∀ e ∈ π, KLArcLe e J → e = J) (δ : Fin n → Zd d L) : BASigmaPi d L n M t σ π δ = ∑ u : Zd d L, ∑ w : Zd d L, BASigmaPi d L (KLwIn J + 1) M t (sigmaIn σ J) ∅ (BAdeltaIn J δ u) * ((t : ℂ) * BAThetaOf
    M t (σ J.1) (σ J.2) u w) * BASigmaPi d L (n - KLwIn J + 1) M t (sigmaOut σ J) ((π.erase J).image (KLshiftOut J)) (BAdeltaOut J δ w) := by
L244: theorem baSig_transl {ι : Type} (d n : ℕ) [NeZero n] (L : ι → ℕ) [∀ i, NeZero (L i)] (g E : ι → ℝ) (m : ι → ℂ) (t : ι → ℝ) : (∀ (i : ι) (σ : Fin n → Bool), (∀ j, σ j ≠ σ (j + 1)) → ∀ (c : Zd d (L i)) (δ : Fin n → Zd
    d (L i)), BASig d n L g E m t i σ (fun j => c - δ j) = BASig d n L g E m t i σ δ) ∧ (∀ (i : ι) (σ : Fin n → Bool), (∀ j, σ j ≠ σ (j + 1)) → ∀ (δ : Fin n → Zd d (L i)) (c : Zd d (L i)), BASig d n L g E m t i σ
    (fun j => δ j + c) = BASig d n L g E m t i σ δ) :=
```
Compiled nonempty instances, heads of the `example`s by `python3 insts.py` (`M0` = `BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)`, `P` the flow point of `MFixedPoint.lean:893`; full text in the files):
```
--- RBM3D/BA/KCactusCut.lean
L1270: example := baCactus_cut (d := 3) (L := 4) (F := {((0 : Fin 4), (2 : Fin 4))}) (J := ((0 : Fin 4), (2 : Fin 4))) KCactusCut_isTSP_F02 (by norm_num) (Finset.mem_singleton_self _) (M0) (1 / 2) ![true, true, false, true] ![![0, 0, …
L1280: example := baCactus_leafW_in (d := 3) (L := 4) (n := 4) (J := ((0 : Fin 4), (2 : Fin 4))) (by norm_num) (M0) (1 / 2) ![true, true, false, true]
L1283: example := baCactus_leafW_out (d := 3) (L := 4) (n := 4) (J := ((0 : Fin 4), (2 : Fin 4))) (by norm_num) (M0) (1 / 2) ![true, true, false, true]
--- RBM3D/BA/KMolecule.lean
L382: example := baK_eq_sum_Kpi 3 P.real.1.1 P.g0_pos (L := 4) (by norm_num) 2 P.real (t := 1 / 2) ⟨by norm_num, by norm_num⟩ (n := 4) (by norm_num) ![true, true, false, true] ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]]
L387: example := baKpi_eq_sum_SigmaPi (d := 3) (L := 4) (n := 4) (M0) (1 / 2) ![true, true, false, true] ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]] {((0 : Fin 4), (2 : Fin 4))}
L393: example := baSigmaPi_cut (d := 3) (L := 4) (n := 4) (J := ((0 : Fin 4), (2 : Fin 4))) (by norm_num) (M0) (1 / 2) ![true, true, false, true] (F₀ := {((0 : Fin 4), (2 : Fin 4))}) (by rw [TSP_four]; simp) (π := {((0 : Fin 4), (2 : …
L401: example := baSigmaPi_shift (d := 3) (L := 4) (n := 4) (M0) (fun σ x y c => BAMsigma_shift 3 4 P.g0 _ P.m0 σ x y c) (1 / 2) ![true, true, false, true] {((0 : Fin 4), (2 : Fin 4))} ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]] …
L406: example := baSigmaPi_reflect (d := 3) (L := 4) (n := 4) (M0) (fun σ x y c => BAMsigma_shift 3 4 P.g0 _ P.m0 σ x y c) (KMolecule_BAMsigma_symm 3 4 P.g0 _ P.m0) (1 / 2) ![true, true, false, true] {((0 : Fin 4), (2 : Fin 4))} …
L416: example := (baSig_transl (ι := Unit) 3 4 (fun _ => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => (1 : ℝ) / 2)).1 () ![true, false, true, false] (by decide) ![1, 0, 0] ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]]
L422: example := (baSig_transl (ι := Unit) 3 4 (fun _ => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => (1 : ℝ) / 2)).2 () ![true, false, true, false] (by decide) ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]] ![1, 0, 0]
L429: example (h3 : ∀ Q : ℕ, Q ≤ 2 * (3 - 1) → ∃ C : ℝ, 0 < C ∧ ∀ (σ : Fin 4 → Bool), (∀ j, σ j ≠ σ (j + 1)) → ∀ (r : Fin 4) (x : Zd 3 4), ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 4 => δ r = x), Sig0 () σ δ‖ ≤ C * (1 - (1 : ℝ) …
L444: example (Bp : Unit → ℝ) : Prop := IndStepAbs 3 4 (fun _ : Unit => 4) Bp Sig0 (fun _ s s' => BAThetaOf (M0) (1 / 2) s s')
```

### (b3) Narrative
1. **Result.** Both modules build clean (`lake build`, `lake env lean`: exit 0, no diagnostics); the 17 public declarations are on the standard axioms; the check file compiles; the branch diff is the two sole files; no `sorry`/`admit`/`native_decide`/`axiom`. Registry pre-check: exit 0, the premise ledgers are identical to the run without the new modules (the counts grow by 14 theorems and 8 definitions): no registry edit.
2. **Size.** Combined 1737 lines against the binding 2000 (1733 at the polish commit, +4 for the last `example`); (b1) estimated central 1620, high 1800. Both decision points passed (after C4: `KCactusCut` 1194 ≤ 1350; after M2: 1457 ≤ 1800); every section commit is in the table above. `KCactusCut` copies 914 raw lines of K05b (`KTreeRep.lean` `:106-146`, `:262-1136`, commit ab54184; the plan counted 938 raw); the other 374 lines are new (§1 header and the four public defs, §6-§9).
3. **`KCactusCut`.** The copied helpers keep their proofs. Changes: the charges of the polygons are the merged `sigmaIn`, `sigmaOut` (`KLSumZeroWard.lean:70, 75`), and `BAinVinv J k` is defined as `⟨min (J.1 + k) (n - 1), _⟩`, so `sigmaIn σ J k = σ (BAinVinv J k)` holds by `rfl`; the `Lists` section and the private defs `σIn σOut aIn aOut` of K05b are not copied; `BAdeltaIn/BAdeltaOut` are polymorphic in the codomain (labels and leaf weights). `baCactus_cut` is `KLgval_split` after the slot relabelling `KCactusCut_eN`, `KCactusCut_eL`, `KCactusCut_eE` (cycle compatibility `KCactusCut_φ_next`, `KCactusCut_ψ_next`), with the new `KCactusCut_in_part/out_part` in place of K05b's Θ-specific ones; no `Θ`-swap is needed in it.
4. **K10 fit.** K05b's `KTreeRep_cut` is the case `Lw = Θ`, `P = Q = Θ`, `S = 1`: the scratch file `k10check.lean` (exit 0) derives it from `baCactus_cut` and the two public leaf identities `baCactus_leafW_in/out`, where the reversed inner leaf `Θ^{(σ_j,σ_i)} = (Θ^{(σ_i,σ_j)})ᵀ` holds for any `M` (`KCactusCut_Theta_swap`).
5. **`KMolecule`.** First stage: the generic identity `KMolecule_gval_eq_sum` (twin of `KLtreeValW_eq_sum_selfW`); `baK_eq_sum_Kpi` is `baTreeRep` at `Λ := g` plus the fibres of `F ↦ KLFlong F σ` (`KMolecule_sum_TSPlong`, copy of the private `KLsum_TSPlong`). Clauses: one lemma for a permutation `e` of the labels (`KMolecule_gval_perm`, `KMolecule_theta_perm` by `Matrix.inv_submatrix_equiv`, no invertibility), used at `Equiv.addRight c` and `Equiv.subLeft c`; the reflection needs `hsymm`, discharged at the BA data by the merged `BAMB_symm` (used directly: the 1a planned a copy) and `BAMsigma_shift`. Factorisation: `KMolecule_tree_cut` (`baCactus_cut` at `Lw = 1`, `P = Q = 1`, `S = tΘ^{(σ_i,σ_j)}`; `1ᵀ = 1`, so C2 needs no symmetry of `M`), the layer bijection `Flong_eq_iff_cut` + `KLsum_cut` as in `Qlayer_cut` (`KLSumZeroWard.lean:293`), and the fourfold sum swap `KMolecule_sum4`.
6. **Against the 1a table.** Every public statement is the 1a's, with: (i) `BAdeltaIn/Out` polymorphic in the codomain (the 1a's definition is `α = Zd d L`); (ii) `BASigmaTree d L M t F σ δ` has `n` implicit; (iii) `baSig_transl` carries the alternation hypothesis exactly as the first two conjuncts of `SigSumZeroAbs`, the proof does not use it (`baSigmaPi_shift/reflect` hold for every `σ`, `π`); (iv) `baCactus_leafW_in/out` are added (Amend 1, public helpers for K10; not in the 1a table); (v) the chord factor is written `(t : ℂ) * Θ u w`, i.e. `(tΘ)_{uw}`, `u` the inner end. Section (a) stands; no `(a′)`.
7. **Consumers.** K07: `BAKpi`, `baK_eq_sum_Kpi` (its `π = ∅` term), `BASigmaTree`; K08a/b: `BASig`, `baSig_transl`, `baSigmaPi_cut`; K09b: `BASig` as the `Sig` of `IndStepAbs`/`SigSumZeroAbs` (the interface `example`s state `SigSumZeroAbs` at `BASig`, the bound clause as a hypothesis, and give `BASig` as the `Sig` of `IndStepAbs`); K10: `baCactus_cut`, `baCactus_leafW_in/out`, `baSigmaPi_cut`, `baKpi_eq_sum_SigmaPi`.
8. **Process.** No RBM1D/RBM2D file was read or written (no port, so no RBM1D/RBM2D diff-stat to give); the numerics of (a) were not rerun (the statements are the 1a's, with the differences of item 6; the identities are now proved). Main moved after the branch base 9d5d47d (it is at 1f710ee in the name-clash line); the hub adds `import RBM3D.BA.KCactusCut` and `import RBM3D.BA.KMolecule` at merge.

### (c) Verified Mathlib names used (`#check @name` in `scratchpad/T2376/1b/names.lean`, exit 0; none searched and found absent)
- Equiv.subLeft : {G : Type u_1} → [AddGroup G] → G → G ≃ G
- Equiv.addRight : {G : Type u_1} → [AddGroup G] → G → Equiv.Perm G
- Equiv.piCongrRight : {α : Sort u_1} → {β₁ : α → Sort u_2} → {β₂ : α → Sort u_3} → ((a : α) → β₁ a ≃ β₂ a) → ((a : α) →
- Fintype.sum_equiv : ∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [Fintype ι] [Fintype κ] [AddCommMonoid M] (e : ι ≃ 
- Matrix.inv_submatrix_equiv : ∀ {m : Type u_1} {n : Type u_2} {α : Type u_3} [Fintype n] [DecidableEq n] [CommRing α] [
- Matrix.nonsing_inv_eq_ringInverse : ∀ {n : Type u_1} {α : Type u_2} [Fintype n] [DecidableEq n] [CommRing α] (A : Matr
- Finset.prod_univ_sum : ∀ {ι : Type u_1} {R : Type u_2} [CommSemiring R] [DecidableEq ι] {κ : ι → Type u_3} [Fintype ι]
- Fintype.piFinset_univ : ∀ {α : Type u_1} {β : α → Type u_2} [DecidableEq α] [Fintype α] [(a : α) → Fintype (β a)], (Fi
- Finset.sum_fiberwise_of_maps_to : ∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [AddCommMonoid M] {s : Finset ι} {t :
- Finset.sum_mul_sum : ∀ {ι : Type u_1} {κ : Type u_2} {R : Type u_3} [NonUnitalNonAssocSemiring R] (s : Finset ι) (t : 
- Finset.sum_comm : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : 
- Finset.sum_filter : ∀ {ι : Type u_1} {M : Type u_2} {s : Finset ι} [AddCommMonoid M] (p : ι → Prop) [DecidablePred p] 
- Finset.prod_mul_distrib : ∀ {ι : Type u_1} {M : Type u_2} {s : Finset ι} [CommMonoid M] {f g : ι → M}, ∏ x ∈ s, f x * 
- Function.update_eq_self : ∀ {α : Sort u_1} {β : α → Sort u_2} [DecidableEq α] (a : α) (f : (a : α) → β a), Function.up
- Function.update_self : ∀ {α : Sort u_1} {β : α → Sort u_2} [DecidableEq α] (a : α) (v : β a) (f : (a : α) → β a), Func
- Function.update_of_ne : ∀ {α : Sort u_1} {β : α → Sort u_2} [DecidableEq α] {a a' : α}, a ≠ a' → ∀ (v : β a') (f : (a 
- Function.update_apply : ∀ {α : Sort u_1} [DecidableEq α] {β : Sort u_2} (f : α → β) (a' : α) (b : β) (a : α), Function
- Matrix.one_apply : ∀ {n : Type u_2} {α : Type u_1} [DecidableEq n] [Zero α] [One α] {i j : n}, 1 i j = if i = j then 1
- Matrix.transpose_one : ∀ {n : Type u_2} {α : Type u_1} [DecidableEq n] [Zero α] [One α], Matrix.transpose 1 = 1
- Matrix.smul_apply : ∀ {m : Type u_3} {n : Type u_4} {α : Type u_1} {β : Type u_2} [SMul β α] (r : β) (A : Matrix m n α
- Matrix.conjTranspose_apply : ∀ {m : Type u_2} {n : Type u_3} {α : Type u_1} [Star α] (M : Matrix m n α) (i : m) (j : n
- Matrix.submatrix_apply : ∀ {l : Type u_2} {m : Type u_3} {n : Type u_4} {o : Type u_5} {α : Type u_1} (A : Matrix m n 
- Matrix.transpose_nonsing_inv : ∀ {n : Type u_1} {α : Type u_2} [Fintype n] [DecidableEq n] [CommRing α] (A : Matrix n 
### (d) Open issues and paper-delta candidates
- Open: (1) the third conjunct of `SigSumZeroAbs` (the bound clauses at `BASig`) is K07/K08's pin; it is a hypothesis of the interface `example` only. (2) The K10 fit of `baCactus_leafW_in/out` is checked by the scratch file `k10check.lean` only (not in the repository). (3) No blocker, no registry edit, no change to a frozen or pinned signature.
- `T2376a` (`(eq:molecule-Kpi)`, `A_deterministic_estimates.tex:625-632`): the paper writes the long chord as `t S^{(B)} Θ_t^{(+,-)}`; Lean (`S^{(B)} = I`) has `t Θ_t^{(σ_i,σ_j)}` with `σ_i ≠ σ_j`, both orientations; `Θ^{(σ_j,σ_i)} = (Θ^{(σ_i,σ_j)})ᵀ` for every `M` (`KCactusCut_Theta_swap`), and `Θ^{(σ_j,σ_i)} = Θ^{(σ_i,σ_j)}` for the symmetric BA data (`BATheta_swap`).
- `T2376b` (`(eq:defKpi)`, `:611`): the BA `K^{(π)}`, `Σ^{(π)}` carry no `∏ m(σ_i)` and no power of `W` (the `M`-loops are inside the cactus value, as in `BATreeRep`); the band `KLKpi`, `KLSigmaPi` carry `∏ m(σ_i)` (DECISIONS §23); `W^{-d(n-1)}` stands in `baK_eq_sum_Kpi` only.
- `T2376c` (Amend 1; `(eq:molecule-Kpi)`, `:625`): the Lean form is the recursive one-edge factorisation `baSigmaPi_cut`: the outer factor `BASigmaPi σ_out π'` still carries long edges, and the paper's per-molecule `Σ^{(π)}(t, σ^{(k)}, b^{(k)})` is Lean's `BASigmaPi σ^{(k)} ∅`; the paper writes a product over `r` molecules with `r - 1` chords. `BASigmaPi … π` for `π ≠ ∅` has no paper counterpart.
