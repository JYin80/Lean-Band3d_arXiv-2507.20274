Prover model: claude-sonnet-5-5
## (a) Math preflight — Mon Oct 12 20:38:44 UTC 2026
Stage 1a, design gate G5 (mathematics only, no Lean written). Object: weight `Wt(ℓ)=Π_k 1_{Dm}([ℓ β_k])` on `Γ₀=ofLGraph(fxyPowGraph p)`; `valW`, provenance maps `π`, shadow-molecule property, `E[valW Γ₀ Wt]=Σ_o E[valW Q (Wt∘π)]` at `BAlwData`, coverage, engine, `fxyValD`, bridge. Scripts (Python) in `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2472/`: `{prov,cut,mdecay,lines}.py` with the T2448 model copies (`model.py run.py inv.py strategy.py black.py`).

### (i) Exponent table
| quantity | value | constraint | slack |
|---|---|---|---|
| data hypotheses of `BAWExp` (C1) | `3≤L`, `0≤t<1`, `BASelf d L g0 Em m`; instance `d=3,L=4,W=2`, flow point | exactly these (as `BAframeStepIdentity`, `BALvl1A:85`); no `M=mI`, no smallness | `L-3=1`; `0<t0P<1`, `BASelf` = `flowP_data` (`CouplingWindow:869`) |
| engine parameters | `p=2,c=1/4,K0=2,d=3,D=10` | `0<c`; `K=⌈(D+K0·nM+d(nA-nW)⁺)/c⌉` (`LWLvl1:3981`), `ord P0<K` | `K=40/60/80` on the 16 start terms, `K-ord∈[36,78]` (cut.py) |
| black waved edges, target 8 | `=2=p` at all 16 start terms | `p ≤ n_{W,black}` along `BAReach` (`ba_nWS_ge`, merged) | 0 at the start; `Δ≥0` per step (T2448 (a)) |
| weight | `Wt∈{0,1}`; `BAWExp` holds for every real `Wt` | `\|Wt\|≤1` only at the rooted G3 (L3d2b) | n/a |
| roots | `[root]∈Dm` exactly; root = image of some `β_k` | `hroot`, `Wt≠0 → ∀c,[rep c]∈Dm` (`BAAtom:535-536`) | no `(log W)^{1+ε₁}` shift (G5-a ¶1) |
| coverage | internal shadow molecules of the 16 start terms = `{α_i,β_i}`, each ∋ `β_i` | `BACoverBy β` | 0 uncovered (prov.out line 1) |
| `x~y` start terms | 7 of 16 (`p=1`: 1 of 4; `p=3`: 37 of 64) | (6) is `2p≤ord` only, `3p` needs `ext0≁ext1` (`BALocRegConcl` (a)) | far form unavailable: row (vii) |
| M-decay rate `c=BAct_rate 3 g κ` (`CombesThomas:45`), `κ=Im m`, `E=0,η=0.1` | `g=1/64,1,10`: `c=0.4753, 0.04519, 0.004255` (`Im m=0.9506, 0.5547, 0.5117`) | `c>0`; `λ=ln W` with `cλ^{3/2}-Dλ ≥ N ln(1/c)`, `D=10`, `N=5` | `ln W0=4.4e2, 4.9e4, 5.5e6` (asymptotic in `W`, used by no target) |
| `ℓ_t` | `min(max(ilambda\|1-t\|^{-1/2},1),L) ≥ 1` (`1_2:1122`) | `\|a-b\|>(log W)^{3/2}ℓ_t` (`7_8:1603`) | `(log W)^{3/2}ℓ_t ≥ (log W)^{3/2}` |
| M-dots on the `x`–`y` path | `≤5` (strategy, `K=ord+2`); `≤17` on a node | only the prefactor `c^{-N}` depends on `N` | threshold shifts by `N ln(1/c)` |
| lines | central 2,142 = `BAProv` 847 + `BAProvB` 1,295 | one row ≤ 1,950; each file < 2,000 | −192 (split); +1,153 / +705 |

### (ii) One nondegenerate instance
`p=2,c=1/4,K0=2,d=3,D=10`; data `d=3,L=4,W=2`, `(g0P,EP,t0P,m0P)`; `ℓ0` (`x`=block 0, `y`=block `Pi.single 0 1`, offsets 0, `BASymm1:445`); `Dm∈{univ,{0}}` of 64 blocks; `w_k(x)=1` at `x=0`, `1/2` elsewhere. Every hypothesis holds at once: `3≤4`, `BASelf`, `0<t0P<1` by `flowP_data`; 16 non-empty start terms with `ExtOK`, `CoverBy` (prov.py); a non-empty tree (10,832 nodes: 108 weight, 32 gg, 20 within steps); `Dm={0}` a proper non-empty subset; `Dm=univ` recovers `ba_fxyPow_integral_eq` (`BALocReg1B:294`). No external hypothesis in any target: the binder is discharged by the merged `baShapeLL_e2_tn/macroA_tn/macroB_tn` (`BAShapeO2B:221,269,303`); the only limit statement is (vii), computed below.
```
$ python3 cut.py
p=2 c=1/4 K0=2 d=3 D=10: (ord, nM, nA-nW, K, black waved) -> #start terms; K - ord:
   (2, 0, 0, 40, 2) -> 1 | K-ord = 38
   (2, 1, 1, 60, 2) -> 2 | K-ord = 58
   (2, 2, 2, 80, 2) -> 1 | K-ord = 78
   (3, 0, 0, 40, 2) -> 4 | K-ord = 37
   (3, 1, 1, 60, 2) -> 4 | K-ord = 57
   (4, 0, 0, 40, 2) -> 4 | K-ord = 36
$ python3 prov.py > prov.out   # seed 20261012, 2m02s;  grep -v '^  ' prov.out | cut -c1-250
start terms p=2: 16 | ExtOK (ext ids fixed): True | internal molecules = {alpha_i,beta_i}, covered by beta^(k): True | x~y start terms: 7 of 16
p=1: start terms 4, covered True, x~y 1
p=3: start terms 64, covered True, x~y 37
strategy S' from the 16 start terms, K = ord+2: nodes 10832, output-vs-parent checks 10900, violations 0, truncated False
every BAFrameStep at all 4 twists of random normal parents: steps by kind {'weight': 52522, 'within': 26534, 'edge': 9751, 'gg': 334, 'ggSplit': 40} | outputs checked 4648438 | violations 0 | terms with an unjoined new vertex 0
$ grep 'steps by kind' prov.out | head -1 | cut -c1-200
  steps by kind {'weight': 108, 'gg': 32, 'within': 20} | outputs by x~y {'x!~y': 6894, 'x~y': 4006} | max #M-dots on a node 17 | max M-dots on a shortest ext0-ext1 path 5
$ awk '/^  [a-zA-Z]+ +[A-Za-z.0-9]+ +outputs/{printf "%s.%s:%s/%s ",$1,$2,$4,$6}' prov.out   # outputs checked / violations per constructor
edge.L:19502/0 edge.LD:189024/0 gg.A:3006/0 gg.AD:1264/0 gg.B:2004/0 gg.BD:1264/0 ggSplit.X.L:80/0 ggSplit.X.LD:16/0 ggSplit.X.d:280/0 ggSplit.X.tr:632/0 weight.lw2.D:1207808/0 weight.lw2.leaf:52522/0 weight.lw4.D:1207808/0 weight.lw4.leaf:52522/0 within.W.D:610368/0 within.W.first:26534/0 within.W.tr:1273804/0
$ python3 mdecay.py | sed -n 2,8p     # d=3 L=4 E=0, Lam=g, N=5, D=10
       g    eta       Im m   residual       c=rate         c^-1          ln W0
 0.01562   1.00   0.617784    1.0e-15 3.088920e-01   3.2374e+00   1.049235e+03
 0.01562   0.10   0.950589    1.0e-15 4.752943e-01   2.1040e+00   4.434075e+02
 1.00000   1.00   0.354845    1.0e-15 2.914163e-02   3.4315e+01   1.177566e+05
 1.00000   0.10   0.554668    2.2e-16 4.518593e-02   2.2131e+01   4.898024e+04
10.00000   1.00   0.251349    8.9e-16 2.092381e-03   4.7792e+02   2.284117e+07
10.00000   0.10   0.511681    3.3e-16 4.254940e-03   2.3502e+02   5.523489e+06
$ python3 lines.py
file A (BAProv): band lines 797, header 40, central 847
file B (BAProvB): band lines 882, header 0, central 1295
central total 2142 | prior (T2387 TW, LWProv 1-1820 x 0.85) 1547 | split line 1950: exceeded | stop line per file 2000 | 2.6 x central (TLC-4) = 5569
alternative cut (targets 5(a)+5(b) in BAProv, i.e. the five weighted identities and twist): A = 1467, B = 675
by target (header 40 in BAProv not included): {'1': 25, '4': 301, '6': 332, '7': 125, '8': 123, '9': 100, '10': 120, '5a': 180, '5b': 620, '2+3': 176}
$ PAT='BAProvOut|BACoverBy|BAWExp|BAProvStepPos|BAEngineProv|ba_localregularXP|baEngineProv_imp_localregularX|fxyValD|baProv_|BAGraph\.valW|BAPGraph\.valW|BAProv(B|C)?\b|BAProv_'
$ git grep -c -E "$PAT" main -- RBM3D RBM3D.lean | wc -l ; for b in $(git branch --list 't/T24*' | tr -d ' *+'); do git grep -c -E "$PAT" $b -- RBM3D RBM3D.lean; done | wc -l
0
0      (74 branches t/T24* scanned, including t/T2465 a90e3aaf, t/T2469 ad52b370, t/T2470 a39337f5, t/T2471 a79521fb; t/T2467 = main)
$ awk '/^\/-! ## Part 2/{f=1} f' docs/tickets/checks/T2472-check.lean | grep -cE 'sz\.lam|withLam|Sizes|gK'
0
```
### Fill-in table (H250 (4))
| # | result (line / script) |
|---|---|
| (i) | G5-a below, ¶1–¶6; differences from the band: ¶6. |
| (ii) | New vertices → joining edge (all joined to an old or earlier new vertex; `unjoined 0`, 4,648,438 outputs, 0 violations): `lw2`{leaf,D_q}: α-M-x, β-W-α. `lw4`{leaf,D_q}: z-M-x, y-W-z, α-M-y, β-W-α. `lanlw`{T1,D_q}: α-M-x, β-W-α. `gg2`{A1–A3: u-M-x, β-W-u; A4,A5,D_r: α-M-x, β-W-α}; `gg4`{B1,B2,D_r}: u-M-x, w-W-u, α-M-w, β-W-α. `within`{first,D_q}: α-M-x, β-W-α; `tr`: M(x,α),M(α,y), then `tr.lw2/lw4` join β. `ggSplit`{T1,D_q,d1–d4}: α-M-a, β-W-α; `tr`: M(α,a'), then `tr.gg2/gg4` join β. Twist: identity on vertices. `splitG`: only prepends M-dots. `merge`: `vmap` injective (no `=`-dots). Joining edges kept: `BAGraph.ext` maps waved/psi/mdot (`BAWeightOp:56-59`, `lanlwExt` `BAExpandW:114`). Merged: `BAGraph.twist_atomAdj` (`BASymm1:73`), `lwSymmTwistG_adj` (`LWSymm:328`), `BAAtom_shadow_adj` (`BAAtom:78`). New: one lemma `BAProv_ext_mol` (k new vertices, join hypotheses) with 12 instances. |
| (iii) | prov.py above: from the 16 start terms to `K=ord+2`, `ExtOK`, kept, `mol1`, no-new-molecule, `mol2`, `cover` at every output: 0 violations over 10,900 checks (plus 4.65M random-parent outputs, all 5 kinds, 4 twists); x~y outputs 4,006 of 10,900. |
| (iv) | Per-labelling cores (the new labels are summed inside; multiply by `Wt(ℓe,ℓi)`, sum over `ℓi`). lw: `BAWeightOp_core` `BAWeightOp:418` (private; with `_R` :291, `_sd` :394, `_val2/_val4` :554/559, `_val_tame` :644: `open private`), wrapper to twin. lanlw: `BAExpandW_term_integral` `BAExpandW:638` + `_integral_val2` :801 (public), `lanlw_val` :908. gg: `BAGGOp_core` `BAGGOp:521` (private; `_R` :400, `_baSum_eq` :673). macros: `BALvl1A_macroA_val` :309, `_macroB_val` :403 (termwise algebra, private, twin weighted), `_macroA_graph` :334, `_macroB_graph` :423 (compositions through `lanlw_val` and `baExpFrameE_holds`, private, twin), helpers `_lwSplit_last` :282, `_sum_eraseIdx` :290. twist: `BASymm1_term_twist` `BASymm1:245` (per ℓ, public), `baTwistIntegral_gen` `BASymm2:104` (any F, public). splitG: `BAGraph.val_splitG` `BAVocab:647` over private `BAVocab_split_val` :618 (per ℓ; weighted copy). merge: private `BAVocab_val_eq_merge_val` :811 (+`_term_zero` :746, `_exists_inr_of_int` :803; weighted copy, pattern `lwProv_valW_merge` `LWProv:621`). recursion: private `BALvl1C_aux` :482, `_integral_comb` :466 (copy under the stem with maps). Weighted transport `seqP → PF` by `lwWx_integral` (`LWWeightExp:330`, public). No step identity exists only after the sum over the old labels. |
| (v) | `splitG` of `ofLGraph(fxyPowGraph p)` (`BAVocab:170`; `4^p` terms, 16 at `p=2`: each uncircled `G_{xα_i}`, `G_{α_iy}` circled or M-dotted), `packMerge` (`:220`): `pmap=vmap`, `ExtOK` by the `lwProv_vmap_inl` twin (`LWProv:332`), internal molecules `{α_i,β_i}` (those with neither edge M-dotted) ∋ `β_i`; 7 of 16 have `x~y` (prov.py line 1). Lean statement as `lwProv_fxyCover` (`LWProv:537`) over the partition. |
| (vi) | Probe step (compiles `RBM3D/Probe/T2472Pins.lean`) fills the diff. Texts to compile: `BAProvOut P`={`Q:BAPGraph (Fin 2)`, `π:P.E'⊕P.I'→Q.E'⊕Q.I'`}; `ExtOK`: `π(inl(P.ext i))=inl(Q.ext i)`; `Molecular`: (`molOf v=molOf w → molOf(π v)=molOf(π w)`) ∧ (internal `c` of `Q.g.shadow` → ∃v, ¬ext `P.g.shadow.molOf v` ∧ `molOf(π v)=c`), both on `shadow`; `BACoverBy β`; `BAWExp d P outs` = `∀L W,3≤L → ∀g0 Em t m,BASelf→0≤t→t<1→∀Wt ℓe, ∫P.valW (BAlwData…) Wt ℓe = Σ_o ∫o.Q.valW (BAlwData…) (Wt∘π) ℓe` over `PF d L W 0`; `BAProvStepPos d`: `BALocStep P L → P.g.Normal → ∃ps, ps.map (·.Q)=L ∧ (∀o∈ps,ExtOK∧Molecular) ∧ BAWExp d P ps`; `BAEngineProv`: the check's shape, start `baPG(ofLGraph(fxyPowGraph p))` (`BAAtomic:81`), conjuncts `ExtOK`, shadow cover of `π(inr β_k)`, `BALocRegConcl`, `p ≤ n_{W,black}`, `BAWExp d` on `outs++errs` (Molecular is internal to the recursion); `fxyValD` = LHS of `T2472_FxyDUniv`; target 9(c) LHS = `BAGraph.valW` unfolded (real `S` by `BASymm1_data_real`). |
| (vii) | Decision: M-decay branch, not the shadow branch. Shadow (`BALocReg1_mol_of_atom` `BALocReg1:304`) puts `ext0,ext1` in one molecule, so the aux graph loses `𝒯_t(\|a-b\|∧ℓ)^p` (`BAGtoAGT` has no `hext`, `BAExp14d:269`). M-decay: an `x~y` output has a chain of `n` M-dots from `x` to `y` (psi=[], no `=`-dots; `n≤5` in the model) and `BAMfine_decay` (`GreenSchur:124`) gives `∏‖M‖ ≤ c^{-n}e^{-c\|a-b\|}`; under `(eq:far_ab_K)` (`7_8:1603`; the pin's `zdistInf ≤ zdistD`, `Defs/Sizes:117`) and `ℓ_t≥1` this is `≤ c^{-n}e^{-c(log W)^{3/2}}`; against `W^{-D}` the condition is the (i) row `cλ^{3/2}-Dλ ≥ n ln(1/c)`: `ln W0 = 4.4e2, 4.9e4, 5.5e6` at `g=1/64,1,10` (`Λ=g`, `d=3`, `κ=Im m`, `E=0, η=0.1`; `η=1`: 1.0e3, 1.2e5, 2.3e7). Asymptotic in `W`, as every `≺` statement; L3d4's statements do not use it. L3d4 keeps these outputs in the lists (`2p≤ord`); L3d2b owns one new lemma (M-chain bound from `atomSetoid`, `BAAtomic:132`) and must show the remaining factors are `≤ W^{C}`. Reads no part of (6). |
| (viii) | L3d2b reads (band → BA): `lwMomentExp_wt` `LWMomentExp:379` → own def over `BAProvOut.π`; `lwMomentExp_expand` :390-460 → `BAWExp.prod` (3), `baProv_bridge` (9c), `baStart_nWS` (merged), weighted homogeneity (band `lwMomentExp_pvalW_smul`) → own lemma from `BAExp14d_term_scale` (needs `BAReal`); `LWf_split`/`dom_*` :32-74 → `fxyValD_union` (9b); `lwMomentExp_rep` :1000-1016 → shadow cover conjunct of `BAEngineProv` → `rep` (shape in the check); `lwMomentExp_pin_gen` :1302 (engine call :1325) → `ba_localregularXP` (lists, `BALocRegConcl` (a)(b)(c), `p≤n_{W,black}`, `BAWExp`); `LWGtoAGRooted` `AuxGraphRooted:225-243,362` reads `valW` only → `BAGraph.valW` (1); the BA rooted G3 (from `BAAtom_solid_prod_conf`, `BAGtoAGT`) and `LWfgD` (needs T2470's `LWfg`) are placed in L3d2b. L5: `LWTermHolds:1524` reads `lwMomentExp_holds` only → nothing from `BAProv`. |
| (ix) | UBA-C1: statements 1–10 are at `BAlwData d L W g0 Em t m ω` and `PF d L W 0`; `Part 2` of the check has 0 hits of `sz.lam\|withLam\|Sizes\|gK` (command above); privates reused internally build `lwWxSizes d L W 0 hL` (a construction, not `sz.lam`). Not triggered; a crossing would use R1 (§273 (1)). |
| (x) | `GaussIBP sz` → `gaussIBP` proved inside, not a premise; `0<z.im, 0<u, m≠0, z+um=-m⁻¹, Sp` fixed point, `Spᵀ=Sp`, `M a a=m`, `M a b=0` → none: `BASelf d L g0 Em m`, `0≤t<1`, `3≤L` (new, as `BALvl1A:85`); `t=0` included (both sides vanish per labelling); `P.g.Normal` for stepPos/exists as band; `BAReal` and `3≤d` only in L3d2b. |
| (xi) | Premise scan (`Test/Axioms.lean:391-460`): Prop-defs in public binders: `BAWExp` (`.refl`, `.comp` conclude it), `BACoverBy`, `Molecular`, `ExtOK` (`.comp` of each concludes it); the step and engine statements are `def`s with no visible binder, concluded by `baProv_stepPos`, `ba_localregularXP`; registry: none. `open private` list: (iv) names + `BAExpandW_integrable_PF` :295, `BAVocab_vmap_injective` :1047, `_merge_atomAdj` :1083, `_merge_dotted_eq` :1076; copies under `BAProv_`: `BALvl1C_aux`, `_integral_comb`, `BAVocab_val_eq_merge_val`. |
| (xii) | lines.py above: `BAProv` 847 (header 40; 1: 25, 2+3: 176, 4: 301, 5a: 180, 9: 100, 8b: 25), `BAProvB` 1,295 (5b: 620, 6: 332, 7: 125, 8: 98, 10: 120); total 2,142 > 1,950: **split taken** (`L3d4a`/`L3d4b`). Cut: the ticket's cut gives 847 / 1,295; moving 5(b) into `BAProv` gives 1,467 / 675 (balanced); both < 2,000. TLC-4 `2.6×`: 5,569 for one row, 2,202 / 3,367 per file. A 9% error in the factors puts the total at the line. |
| (xiii) | Switch conditions: (a) not met (no new shadow molecule, no dropped joining edge: prov.py, 0 violations); (b) not met (every step has a per-labelling form, row (iv)). Role stays `prover-hard`. |
| (xiv) | Clash grep above: 0 on `main` c986735f and on all 74 branches `t/T24*`; no `BAProv*` file on `main`. |

### G5-a (the BA argument, provenance half)
¶1 Domain. `Wt` sits on `Γ₀` (per block `i`: loop `Ǧ_{β_iβ_i}`, `G_{xα_i}`, `G_{α_iy}`, waved `α_iβ_i`, ×-dots `α_i≠x,y`; `LocalRegular:1347-1359`). `7_8:1631-1632, 1647-1650` ("all internal vertices of `𝒢^aux` in `D`") is the root form: the aux vertex of an internal molecule is its root, a root is the image of some `β_k`, and `Wt≠0` puts `[root]∈Dm` exactly (`T2289d`, `T2289-prove:96`); this is the `root`/`hroot` input of `BAAtom_solid_prod_conf`. `B:522-524` adds no step: "same reasoning" = this transport on the shadow (`B:415-418`).
¶2 Maps (i). Each output is a term `BAGraph.ext k Γ …` (`BAWeightOp:56`), then `splitG`, `packMerge`, twist: old `v ↦ owxEmb k v ↦ vmap`; twist = id; `inl ↦ inl`; on a Normal parent `vmap` is injective.
¶3 No new molecule (ii), on `BAGraph.shadow` (waved, `=`, Ψ, M edges join; `BAAtom:63,100`). Kept: all old waved/M edges (table (ii)); `splitG` only adds M-dots; twist keeps adjacency. New vertices each have a joining M/waved edge to an old or earlier new vertex. So `mol1`, `nonew`, `mol2` hold by `lwProv_reach_map` (`LWProv:293`, applied to shadows) and the `lwProv_molecular` argument (`:307`); `CoverBy.comp` as `LWProv:137`.
¶4 Per labelling (iii). Every identity of row (iv) is at a fixed labelling of the old vertices; hence multiplying by `Wt` and summing gives the weighted identity with `Wt∘π` for lw, lanlw, gg, macros (a), (b), twist, `splitG`, `merge`; compose by `BAWExp.comp`.
¶5 Start (iv)/(v): row (v). ¶5′ Coverage at every output follows from `CoverBy.comp` along `BAReach`; checked numerically (row (iii)).
¶6 Differences from the band: (1) molecules join by M-dots (shadow), not only waved edges; (2) `splitG` merges molecules, so `mol1` is a monotone map, not injective; (3) no tags and no scalar `m`-partition: `val_eq_partition` has no data hypothesis; (4) `x~y` outputs exist (`2p≤ord` only): (vii); (5) five frame kinds with two composite macros (`within`, `ggSplit`: a transfer graph `tr`, then `lw`/`gg` at `tr`) against three band kinds.

### Verdicts
Targets 1–10: **PASS** (no hypothesis set fails; G5 holds: no new shadow molecule, every step per labelling; central 2,142 > 1,950 so the pre-signed split is taken; no dispatcher sign-off needed). Findings for the 1a-audit: (F1) split and cut choice, row (xii); (F2) `x~y` outputs are handled by an M-chain lemma in L3d2b, threshold asymptotic, row (vii); (F3) weighted homogeneity in L3d2b needs `BAReal`, row (viii).

## (a″) Probe compile — Mon Oct 12 21:32:29 UTC 2026 (probe step, `prover-hard`, claude-sonnet-5-5; section (a) not edited)
Probe file `RBM3D/Probe/T2472Pins.lean` (worktree `RBM3D-wt/T2472`, branch `t/T2472`; never merged, no importer). Script output first.
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2472 && git log -1 --format="%h %an %s" && wc -l RBM3D/Probe/T2472Pins.lean
cf137d01 Jun Yin T2472: probe step (G5-b texts, start coverage at p = 2, molecular outputs of the five frame kinds and the twist)
     399 RBM3D/Probe/T2472Pins.lean
$ git diff --stat HEAD -- RBM3D/Probe/T2472Pins.lean; git show --stat --format= HEAD
 RBM3D/Probe/T2472Pins.lean | 399 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 399 insertions(+)
$ date -u; time lake env lean RBM3D/Probe/T2472Pins.lean; echo exit=$?    # start / end:
Mon Oct 12 21:27:54 UTC 2026
Mon Oct 12 21:30:17 UTC 2026
baEngineProv_imp_localregularX : BAEngineProv → T2472_LocRegXClosed
'RBM.Graph.BAProv_start2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAProv_within_B' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAProv_locStep_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baEngineProv_imp_localregularX' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baEngineProv_imp_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
lake env lean RBM3D/Probe/T2472Pins.lean  136.95s user 6.69s system 99% cpu 2:23.71 total
$ grep -c "sorry\|admit\|native_decide" RBM3D/Probe/T2472Pins.lean; grep -c "^axiom" RBM3D/Probe/T2472Pins.lean; grep -rn "import RBM3D.Probe" RBM3D.lean RBM3D | head -3
0
0
(no output above = no importer)
$ lake env lean <scratch>/T2472/evid.lean   # outputs per step (= terms of the partition of each term of the lists), and the 16 start terms at p = 2; scratch file, not in the repo
("gg P_A", 17, 14)
("weight P_W2", 41, 41)
("edge P_E", 26)
("within P_B", 17, 17, 17)
("ggSplit P_C", 10, 7, 17, 14)
[[0, 1, 2, 3], [2, 3], [2, 3], [2, 3], [0, 1], [], [], [], [0, 1], [], [], [], [0, 1], [], [], []]
("terms with an internal molecule", 7)
("terms with x ~ y", 7)
```
### The four probe items (ticket Probe line): all compile, no `sorry`
| item | probe lines | result |
|---|---|---|
| G5-b texts | 29-98 | `BAGraph.valW`, `BAPGraph.valW`, `BAProvOut`, `ExtOK`, `Molecular`, `comp`, `BACoverBy`, `BAWExp`, `BAProvStepPos`, `BAEngineProv`, `fxyValD`, `BAProv_Bridge` compile; `Molecular.comp`, `BACoverBy.comp`, `BAWExp.refl`, `valW_one` proved |
| `BACoverBy` at the 16 start terms, `p = 2` | 184-196 | `BAProv_start2`: `partition.length = 16`; every `P0` has `o : BAProvOut (baPG (ofLGraph (fxyPowGraph 2)))` with `o.Q = P0`, `ExtOK`, `BACoverBy (fun k => o.π (inr (β k)))`, `π = vmap`. Control (l.195): `β₀` alone does not cover (`¬ ∀ …` by `decide +kernel`). The cover obligation is exercised at the 7 terms with an internal molecule (per-term lists above) |
| `Molecular` of the outputs of each frame kind | 253-298 | one statement per kind: `BAFrameStep P F ∧ ∃ ps : List (BAProvOut P), ps.map (·.Q) = F ∧ ∀ o ∈ ps, o.ExtOK ∧ o.Molecular`, for **all** outputs of the step: `gg` at `P_A` 31, `weight` at the first start term `baPW2` (`E = Fin 2`; `BASimInst.baPW` has `E = Fin 1`) 82, `within` at `P_B` 51, `ggSplit` at `P_C` 48, `edge` at `P_E` 26: 238 outputs (counts above; 31 and 48 agree with `BASim.lean:1971` `ggF.length = 31` and `BASim3.lean:1913` `splitOutsT … .length = 48`). `BAFrameStep` by the merged `hFA hFB hFC hFE` (`weight`: the constructor at `baPW2`, hypotheses by `List.mem_cons_self` and `decide`) |
| twist | 300-341 | `locStepB` (l.328): `BALocStep` + `Normal` (merged `locStepB`, `normalB`) + the 51 `within` outputs twisted, `ExtOK`, `Molecular`; `BAProv_locStep_exists` (l.334): positions of a `BALocStep` from those of its frame step at `P.twist c t` (`ba_twist_inv_out`, `BALvl1A_twist_invol`) |
| `BAEngineProv → T2472_LocRegXClosed` | 134, 142 | first output line above: `baEngineProv_imp_localregularX : BAEngineProv → T2472_LocRegXClosed`, proved |

### Row (vi): the G5-b texts and their diff against the check, compiled
| text | probe line | diff against the check |
|---|---|---|
| `BAGraph.valW`, `BAPGraph.valW`, `valW_one` | 30, 34, 41 | the check's `valW_one` shape is `valW_one` unfolded (`simp [valW, val]`) |
| `BAProvOut`, `ExtOK`, `Molecular`, `BACoverBy` | 45, 49, 51, 56 | as in (a)(vi); `BACoverBy` ranges over `LGraph.AuxIMol P.g.shadow` (the check's form) |
| `BAWExp d P outs`, `BAProvStepPos d` | 71, 79 | as in (a)(vi); data binder `[NeZero L] [NeZero W]`, `3 ≤ L`, `BASelf`, `0 ≤ t < 1` only |
| `BAEngineProv` | 83 | check shape (Σ-pairs) follows: `baEngineProv_imp_shape : BAEngineProv → T2472_EngineShape` (l.367; the shape copied l.358). Extra in the text: `BAWExp d` on `outs ++ errs`; `ExtOK` reads `P.ext = id` at `baPG` |
| `baEngineProv_imp_localregularX` | 134 | conclusion `T2472_LocRegXClosed`, probe l.102 (copied from `T2472-check.lean:299`) |
| `fxyValD` / `T2472_FxyDUniv` | 90 / 144 | `Iff.rfl` with `fxyValD D univ x y = fxyVal D x y` |
| `T2472_FxyDUnion` | 146 | `Iff.rfl` with `fxyValD D (D₁ ∪ D₂) x y = fxyValD D D₁ x y + fxyValD D D₂ x y` |
| `BAProv_Bridge` / `T2472_Bridge` | 94 / 148 | `T2472_Bridge ↔ BAProv_Bridge := Iff.rfl`: unfolding `BAGraph.valW` (weight `Π_k 1_{Dm}`) and `fxyValD` only |
| roots (shape of the check) | 346 | `BACoverBy.rep`: `rep`, `k` with `β (k c) = inr (rep c)` and `molOf (inr (rep c)) = c.1` |

### Findings for the 1a-audit (facts from the compile)
- P1. One Boolean test `BAProv_chk Γ emb T'` (l.208: no `=`-dotted edge; every `Γ.adj` kept under `emb`; every vertex of `T'` in the molecule of some `emb v`; `emb` the identity on `E`) gives `ExtOK` and `Molecular` of the merged, repacked output `ofTerm` (l.204, `BAProv_ofTerm_good` l.213), by `lwProv_reach_map` on shadows, `BAVocab_merge_adj`, `vmap` onto. `BAProv_outsOf_exists` (l.234) turns it into the positions of one `outsOf` list. The test is a Boolean (`List.all`), not a `Decidable (∀ T ∈ Ts, …)`: instance search did not find the latter at terms typed with `(baPG _).E'`. Negative control (l.388): `ext 2` of `P_A` without new edges gives `false`.
- P2. G5 holds at the probe data: all 238 outputs satisfy `BAProv_chk`, hence `Molecular` (no output creates a new shadow molecule or drops a joining edge); 16/16 start terms are covered. Not a proof for all normal `P` (the general `BAProv_chk = true` per constructor is 1b; (a)(iii) remains the evidence for all normal parents). Switch conditions (a), (b) of (a)(xiii) are not met by the probe.
- P3. Generic lemmas used by all families: l.152-180, 200-243, 300-341 (115 lines). Not re-priced: (a)(xii) is unchanged.
- P4. `open private` used in the probe: `BAVocab_merge_adj` (`BAVocab:1092`), `BAVocab_vmap_surjective` (`:1052`); (a)(xi) lists `BAVocab_vmap_injective :1047`, `_merge_atomAdj :1083`, `_merge_dotted_eq :1076`, so add these two.
- P5. `BAProvOut.ofTerm` repacks with the merged `BALvl1A_pcomp` (`BALvl1A:120`), the literal of `BAPGraph.outsOf`; `ps.map (·.Q) = P.outsOf Ts` by `simp` (inside `BAProv_outsOf_exists`). The twist needs no `BAReal`: `BAProv_twist_mol_iff` (l.305) says the molecules of `Γ.twist c t` are those of `Γ`.
- P6. Cost: `lake env lean` takes 2:23 (kernel evaluation of the 238 outputs); two statements (`within`, `ggSplit`, l.272, 283) need `set_option maxHeartbeats 1000000` for the unification of the unfolded `withinOuts`/`splitOuts` lists. This concerns the instances only (target 10), not the general proofs.
- P7. Only `BAWExp.refl` is proved here; the weighted identities (target 5) and the other `BAWExp` constructors are 1b. No hypothesis was added, no pinned signature changed.

### Fill-in table (H250 (4)): all 14 rows filled
Rows (i)-(v), (vii)-(xiv) in (a); row (vi) above; row (xi) addendum P4. Probe step verdict: **PASS** (exit 0, axioms `propext`, `Classical.choice`, `Quot.sound`, 399 lines ≤ 400).

## (b) Stage 1b, L3d4a (`RBM3D/Graph/BAProv.lean`): script output, written Mon Oct 12 22:17:42 UTC 2026
Scope: the dispatcher's instruction after the 1a-audit confirmed the pre-signed split (`T2472-1a-audit.md:133`): this stage delivers **L3d4a = `Graph/BAProv`, targets 1-4, 5 (a), 9**.
Targets 5 (b), 6, 7, 8, 10 (L3d4b, `BAProvB`) are **not delivered here**; they run later on a branch stacked on `t/T2472`. The `prover-max` switch was checked first: 1a-audit §8 and (a) row (xiii) say not triggered; nothing below contradicts them. (a), (a″) not edited; no (a′) needed.
```
$ TZ=UTC git log --format='%h %ad %s' --date=format-local:'%Y-%m-%d %H:%M:%S UTC' -6   # t/T2472: the first 5 lines are stage 1b, the 6th (cf137d01) is the probe step
e7ada40a 2026-10-12 22:17:05 UTC T2472: BAProv keeps a private copy of pow_conj (no Sizes name in the fil
73ab0a12 2026-10-12 22:14:45 UTC T2472: BAProv reuses lwMoment_pow_conj in the bridge
f643c171 2026-10-12 22:10:31 UTC T2472: BAProv drops the unused BALocReg1B import
1ff3c984 2026-10-12 22:07:45 UTC T2472: BAProv sections 6-7 (domain form of f_xy, bridge, compiled instan
f1ca6549 2026-10-12 21:52:14 UTC T2472: BAProv sections 1-5 (weighted values, provenance outputs, BAWExp,
cf137d01 2026-10-12 21:30:34 UTC T2472: probe step (G5-b texts, start coverage at p = 2, molecular output
$ wc -l RBM3D/Graph/BAProv.lean   # stop size 2,000; sections: 1 l.49, 2 l.86, 3 l.141, 4 l.175, 5 l.553, 6 l.675, 7 (instances) l.759
877 RBM3D/Graph/BAProv.lean
$ lake build RBM3D.Graph.BAProv   # the committed file e7ada40a, started Mon Oct 12 22:15:54 UTC 2026
✔ [3950/3950] Built RBM3D.Graph.BAProv (5.0s)
Build completed successfully (3950 jobs).
$ lake env lean axioms_A.lean      # #print axioms of all 67 public theorem/def/structure/abbrev declarations of the file (names by script)
67 output lines; 67 with exactly [propext, Classical.choice, Quot.sound]; 0 other
$ lake env lean assert_root_A.lean # import RBM3D; import RBM3D.Graph.BAProv; #assert_rbm_axioms  (the ticket's pre-check)
assert exit=0
axiom audit: 13685 theorems, 4370 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
```
Target statements, extracted by script (`extract_stmts.py`: file line, declaration up to `:=`, cut at 158 characters):
```
52: def BAGraph.valW {ι E I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (D : BALData ι) (Wt : (E ⊕ I → ι) → ℝ) (ℓe :  …
57: def BAPGraph.valW {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type} (P : BAPGraph E) (D : BALData ι) (Wt : (P.E' ⊕ P.I' → ι) → ℝ) (ℓe : E → ι) : ℂ
67: theorem BAPGraph.valW_one {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type} (P : BAPGraph E) (D : BALData ι) (ℓe : E → ι) : P.valW D (fun _ => 1) ℓe =  …
89: structure BAProvOut (P : BAPGraph (Fin 2)) where
98: def BAProvOut.Molecular {P : BAPGraph (Fin 2)} (o : BAProvOut P) : Prop
104: theorem BAProvOut.Molecular.comp {P : BAPGraph (Fin 2)} {o : BAProvOut P} {o' : BAProvOut o.Q} (h : o.Molecular) (h' : o'.Molecular) : (o.comp o').Mole …
118: def BACoverBy {P : BAPGraph (Fin 2)} {κ : Type} (β : κ → P.E' ⊕ P.I') : Prop
122: theorem BACoverBy.comp {P : BAPGraph (Fin 2)} {κ : Type} {β : κ → P.E' ⊕ P.I'} (h : BACoverBy β) {o : BAProvOut P} (ho : o.Molecular) : BACoverBy (P
145: def BAWExp (d : ℕ) (P : BAPGraph (Fin 2)) (outs : List (BAProvOut P)) : Prop
152: theorem BAWExp.refl (d : ℕ) (P : BAPGraph (Fin 2)) : BAWExp d P [⟨P, id⟩]
156: theorem BAWExp.comp {d : ℕ} {P : BAPGraph (Fin 2)} {outs : List (BAProvOut P)} (h : BAWExp d P outs) (outs' : ∀ o : BAProvOut P, List (BAProvOut o.Q))  …
166: theorem BAWExp.prod {d p : ℕ} {outs : List (BAProvOut (baPG (BAGraph.ofLGraph (fxyPowGraph p))))} (h : BAWExp d (baPG (BAGraph.ofLGraph (fxyPowGraph p) …
474: theorem BAProv_frameStep_pos (P : BAPGraph (Fin 2)) (hD : ∀ e ∈ P.g.dotted, e.eq = false) {F : List (BAPGraph (Fin 2))} (h : BAFrameStep P F) : BAProvP …
510: theorem BAProv_locStep_pos {P : BAPGraph (Fin 2)} {L : List (BAPGraph (Fin 2))} (hL : BALocStep P L) (hN : P.g.Normal) : BAProvPos P L
520: theorem BAProv_start (p : ℕ) : ∀ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition, ∃ o : BAProvOut (baPG (BAGraph.ofLGraph (fxyPowGraph p))), o.Q = P0 …
668: theorem BAGraph.valW_partition (Γ : BAGraph E I) (D : BALData ι) (Wt : (E ⊕ I → ι) → ℝ) (ℓe : E → ι) : Γ.valW D Wt ℓe = (Γ.splitG.map fun Δ => Δ.packMe …
678: def fxyValD {d L W : ℕ} [NeZero L] [NeZero W] (D : LData (Idx d L W)) (Dm : Finset (Zd d L)) (x y : Idx d L W) : ℂ
682: theorem fxyValD_univ {d L W : ℕ} [NeZero L] [NeZero W] (D : LData (Idx d L W)) (x y : Idx d L W) : fxyValD D Finset.univ x y = fxyVal D x y
687: theorem fxyValD_union {d L W : ℕ} [NeZero L] [NeZero W] (D : LData (Idx d L W)) {D₁ D₂ : Finset (Zd d L)} (h : Disjoint D₁ D₂) (x y : Idx d L W) : fxyV …
707: theorem baProv_bridge (d L W : ℕ) [NeZero L] [NeZero W] (g0 Em t : ℝ) (m : ℂ) (ω : Ω d L W) (p : ℕ) (hp : Even p) (Dm : Finset (Zd d L)) (ℓe : Fin 2 →  …
```
Statement diff against the probe texts fixed at the 1a-audit (`stmtdiff.py`: declarations of `RBM3D/Probe/T2472Pins.lean` and `BAProv.lean`, docstrings stripped, whitespace normalised):
```
14 SAME, 0 DIFF: BAGraph.valW BAPGraph.valW BAGraph.valW_one BAProvOut BAProvOut.{ExtOK,Molecular,comp,Molecular.comp} BACoverBy BACoverBy.{comp,rep} BAWExp BAWExp.refl fxyValD
pins: BAProv.lean:847,852,861 are `example : <T2472_FxyDUniv | T2472_FxyDUnion | T2472_Bridge, body copied by script from docs/tickets/checks/T2472-check.lean> := @fxyValD_univ | @fxyValD_union | @baProv_bridge`;
they elaborate, so the three pins equal 9 (a)-(c) up to the unfolding of `fxyValD` and `BAGraph.valW` (definitional equality). 8 (a)/(b) and `BAProvStepPos` are in L3d4b.
```
Compiled instances (section 7, all `example`s; `d = 3`, `L = 4`, `W = 2`, flow point `(g0P, EP, t0P, m0P)` with `flowP_data`, labels `ℓ0`; every hypothesis discharged, no external premise):
```
767  target 9: fxyValD univ = fxyVal; univ = {0} + univ\{0} (disjoint); bridge at p = 2, Dm = {0} (x in block 0, y in block Pi.single 0 1), for every sample ω
780  target 9 (c) at Dm = univ: the weight is 1, val of the start graph = ‖fxyVal‖^2 (the pointwise form of ba_fxyPow_integral_eq)
786  target 5 (a): splitG.length = 16 and the weighted partition identity at the weight Π_k 1_{0}([β^(k)])
795  target 4, start: partition.length = 16; BAProv_start 2 (ExtOK, Molecular, BACoverBy at the 16 start terms); control: β_0 alone does not cover (decide +kernel)
806  target 3: BAWExp.prod at the flow point, w_k(x) = 1 at x = ℓ0 0 and 1/2 elsewhere (BAProv_w); its hypothesis is the leaf BAWExp.refl (one output, id). 814: BAWExp.comp of two leaves
821-842  target 4: BAProvPos at gg (P_A, ggF.length = 31), within (P_B), ggSplit (P_C), edge (P_E), weight (first start term, E = Fin 2), and locStepB (twist of P_B); lists non-empty
```
Greps, name clash, `open private`, ports:
```
$ grep -nE "sz\.lam|withLam|Sizes|gK" RBM3D/Graph/BAProv.lean | wc -l
       0
$ grep -cE "BAShapeLL|BAFrameStepTN|T2472_Binder" RBM3D/Graph/BAProv.lean
0
$ grep -cE "sorry|admit|native_decide|^axiom|^inductive" RBM3D/Graph/BAProv.lean
0
$ grep -rln "RBM3D.Graph.BAProv\|Probe.T2472Pins" RBM3D.lean RBM3D | grep -v own-files | wc -l   # importers outside the two files
       0
$ git diff --name-only main...t/T2472
RBM3D/Graph/BAProv.lean
RBM3D/Probe/T2472Pins.lean
$ git status --short | wc -l
       0
$ PAT='BAGraph\.valW|BAPGraph\.valW|BAProvOut|BACoverBy|BAWExp|BAProvPos|fxyValD|baProv_bridge|valW_partition|BAProv_|BAProv(B|C)?[^A-Za-z_]'; git grep -c -E "$PAT" <ref> -- RBM3D RBM3D.lean   # Mon Oct 12 22:14:59 UTC 2026
main ae791953: 0 files; scanned 77 branches t/T24* other than t/T2472: 0 hits; sanity t/T2472: BAProv.lean, Probe/T2472Pins.lean
`open private` (BAVocab.lean :line of the private declaration): BAVocab_merge_adj :1092, BAVocab_vmap_surjective :1052, BAVocab_term_merge :775, BAVocab_term_zero :746, BAVocab_good_eq_of_cls :722,
BAVocab_exists_inr_of_int :803, BAVocab_vmap_inr_int :798, BAVocab_vmap_inr_ext :793, BAVocab_split_val :618; BAWeightOp.lean: BAWeightOp_ext_adj :1063. No private deleted, no merged file edited; one private helper of the file (`BAProv_pow_conj`).
Ports: none from RBM1D/RBM2D (no diff-stat owed). Twins of RBM3D's own band `Graph/LWProv.lean` (`valW/pvalW :45-61`, `ProvOut :66-80`, `WExp :82-130`, `CoverBy :132-142`, `LWfD :190-208`, `lwProv_bridge :233-280`,
`lwProv_valW_merge :621-678`, `lwProv_valW_partX :809`), cited in the docstrings of the file.
```
Narrative
- Role and scope as above. The G5 argument is (a) ¶1-¶6; 1b turned its numerics into theorems for **every** parent whose dotted edges are `=`-free (weaker than `Normal`), not only at the probe instances.
- The probe's Boolean test `BAProv_chk` (decided at instances) is replaced by the Prop `BAProv_Ext Γ emb T` (no `=`-dotted edge, `Γ.adj` kept under `emb`, `emb` fixed on `E`, every vertex shadow-joined to an image).
  `BAProv_reach_map` and `BAProv_merge_reach` are the probe's lemmas; `BAProv_ofTerm_good` takes the Prop in place of the Boolean.
- `BAProv_Ext_ext2` / `_ext4`: an extension by 2 (resp. 4) new vertices is a `BAProv_Ext` if vertex 0 is `M`-joined to the image of an old vertex and 1 is waved-joined to 0 (resp. the chain M, W, M, W); the adjacency of `BAGraph.ext` is the merged private `BAWeightOp_ext_adj` (`open private`).
  The families lw2, lw4, lanlwT1/lanlwD, gg2, gg4 are `BAProv_Ext_lw2 … _gg4` (membership by `simp`, then the lemma); `within` and `ggSplit` add their transfer-graph families by `BAProv_Ext.trans` (embeddings `owxEmb 2 ∘ owxEmb 2`, `owxEmb 4 ∘ owxEmb 2`).
- `BAProv_outsOf_exists`: `splitG` (`BAProv_Ext.splitG`), `merge`/`packMerge` (`vmap` onto, `BAProv_merge_reach`) and the repacking of `outsOf` give the positions with `ExtOK ∧ Molecular`; `BAProv_frameStep_pos` is the case split over the five `BAFrameStep` kinds;
  `BAProv_twist_pos` / `BAProv_locStep_pos` carry them through the twist (identity on vertices; the molecules are unchanged, `BAProv_twist_mol_iff`).
- `BAProv_start p` (all `p`): `ofTerm` at `emb = id` for each term of `splitG` of `ofLGraph (fxyPowGraph p)`; the cover is the waved edge `α_i β_i` (as `lwProv_fxyCover`). The `p = 2` probe instance is now one application.
- Weighted partition (5 (a)): `BAProv_term_splitG` (per labelling, from the private `BAVocab_split_val`), `BAProv_valW_splitG`, `BAProv_valW_merge` (weighted copy of the private `BAVocab_val_eq_merge_val` :811), `BAProv_valW_packMerge`, `BAGraph.valW_partition`; no data hypothesis.
- Bridge (9 (c)): the band's argument with `D1.S = 1_{Dm}(blk ·) · S` and `fxyPowGraph_val_eq`; `S` is real at `BAlwData` by `BAlwS`; `‖·‖^p` by `BAProv_pow_conj`.
- Lines: 877 in all (sections 1: 37, 2: 55, 3: 34, 4: 378, 5: 122, 6: 84, 7: 119, header 48) against 847 central of (a) row (xii) and the stop size 2,000; 8 (b) is in L3d4b as the ticket places it. No third row.
- Not here (L3d4b / L3d2b): 5 (b), `BAProvStepPos`, `baProv_stepPos`, `baProv_exists`, `BAEngineProv`, `ba_localregularXP`, 8 (b), target 10; the carrier forms, the BA rooted G3, the M-chain bound for the `x ~ y` outputs ((a) row (vii), 1a-audit O4).

Hypothesis table (premise, band discharge, BA discharge; C1):
| result | premises | band | BA |
|---|---|---|---|
| `BAWExp d P outs` (`.refl`, `.comp`, `.prod`) | `3 ≤ L`, `BASelf d L g0 Em m`, `0 ≤ t < 1`, all real `Wt` | `GaussIBP`, `M = mI`, flow | binder of the def; `.refl`/`.comp` conclude it; no smallness of `g`, no `M = mI` |
| `BAProv_*_pos`, `BAProv_frameStep_pos` | `P.g.dotted` has no `=` edge | `Normal` | weaker than `Normal`; `BAProv_locStep_pos` takes `P.g.Normal` as `BAProvStepPos` does |
| `BAProv_start p` | none | none | none |
| `BAProv_outsOf_exists` | `∀ T ∈ Ts, BAProv_Ext P.g emb T` | — | proved for each family above |
| `BAGraph.valW_partition` (+ `BAProv_valW_*`) | none (pointwise in `ℓe`, any `D : BALData`) | `hM : D.M x x = m` | none (`BAVocab_split_val` has none) |
| `baProv_bridge` | `Even p` | `Sizes`, `hp` | `Even p`; `S` real from `BAlwS` |
| `fxyValD_univ`, `fxyValD_union` | `Disjoint D₁ D₂` (union) | same | same |

Interface table for L3d2b and L5 (final names; replaces the names of `T2472-1a-audit.md` §7 where they differ):
| band consumer | BA name | file |
|---|---|---|
| `lwMomentExp_expand` :390-460 (`WExp.prod` :404, `lwProv_bridge` :412) | `BAWExp.prod`, `baProv_bridge`, merged `baStart_nWS` | `BAProv` |
| `LWf_split`, `dom_*` :32-74 | `fxyValD`, `fxyValD_union`, `fxyValD_univ` | `BAProv` |
| `valW` norm lemmas :289-367; `AuxGraphRooted` :225-243, 362 (`valW` only) | `BAGraph.valW`, `BAGraph.valW_one` | `BAProv` |
| `lwMomentExp_rep` :1000-1016 | `BACoverBy.rep` (from the `BACoverBy` conjunct of `BAEngineProv`), `BACoverBy.comp` | `BAProv` / L3d4b |
| `lwMomentExp_wt` :379; homogeneity :256-287 | own def over `BAProvOut.π`; own lemma from `BAExp14d_term_scale` (`BAReal`) | L3d2b |
| `lwMomentExp_pin_gen` :1302-1345 | `ba_localregularXP` | L3d4b |
| `LWTermHolds` :1524 (L5) | nothing from `BAProv*` | none |

## (c) Verified Mathlib names used (`#check @…` of each in `mathlib_chk.lean`: 51 identifiers, 0 errors; none invented, none found absent)
SimpleGraph.Adj.reachable, Reachable.refl, ConnectedComponent.eq, ConnectedComponent.ind; Finset.disjoint_left, mem_image, mem_univ, prod_congr, prod_mul_distrib, subset_univ, sum_add_distrib, sum_congr, sum_eq_zero, sum_image, sum_subset;
List.any_append, any_eq_true, length_map, map_append, map_congr_left, map_flatMap, map_map, mem_append, mem_cons, mem_cons_self, mem_flatMap, mem_map, not_mem_nil, prod_append, sum_map_mul_left; Complex.conj_ofReal, mul_conj', ofReal_prod, star_def;
Bool.or_eq_true, Classical.choose, Classical.choose_spec, Fin.ext, Function.comp_apply, Function.comp_def, Function.Injective, Sum.elim, Sum.elim_inl, Sum.elim_inr, even_two, mul_pow, pow_mul.

## (d) Open issues and paper-delta candidates
- Open: L3d4b (`BAProvB`: 5 (b), `BAProvStepPos`/`baProv_stepPos`, `baProv_exists`, `BAEngineProv`/`ba_localregularXP`, 8 (b), target 10) is the next row; it imports `BAProv` and reuses `BAProvPos`, `BAProv_frameStep_pos`, `BAProv_locStep_pos`, `BAProv_start`, `BAGraph.valW_partition`, `BAProv_valW_*`.
- Open (from the 1a-audit, unchanged): the `x ~ y` outputs stay in the lists (`2p ≤ ord`); L3d2b owns the M-chain bound, asymptotic in `W` (O4). `BAProvPos` is a new `abbrev` (not in the probe).
- T2472a (Lean/paper): `7_8:1631-1650`, `B:522-524`, "every internal vertex of the auxiliary graph lies in `D`", is the weight `Π_k 1_{Dm}([β^(k)])` on the start graph carried along provenance maps; the root of an internal shadow molecule is the image of some `β^(k)` and `[root] ∈ Dm` exactly (no `(log W)^{1+ε₁}` shift).
- T2472b (Lean/paper): molecules of a BA graph are read on `BAGraph.shadow` (waved, `=`-, `Ψ`-, `M`-dotted edges join; DECISIONS §275 (5)); `BACoverBy` and `Molecular` are stated there (relates to T2287b).
- T2472c (Lean/paper): the provenance expansion `BAWExp` is pointwise-labelled at the data level `BAlwData d L W g0 Em t m ω`, law `PF d L W 0`, for every real weight on the vertex labellings; the domain form `fxyValD` and the bridge are at the data level (no `Sizes`); the `M`-dotted terms of `G = Ǧ + M` carry no tag and no `m`-partition.
