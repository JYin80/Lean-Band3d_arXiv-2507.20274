Auditor model: claude-opus-5-5
# T2131 audit (round 1): LW-08a `Graph/LWSymm`. Sun Oct  4 12:15:12 UTC 2026
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2131-audit1`, detached at `t/T2131` = `6d9aae1`. Scratch: `scratchpad/T2131/`.
The check file `docs/tickets/checks/T2131-check.lean` has `#check`s only, so it pins no statement. Each target is checked against the ticket's mathematics.

## 1. Build, axioms, hygiene, scope
```
$ lake build RBM3D.Graph.LWSymm 2>&1 | grep -E "error" ; tail -1
Build completed successfully (3364 jobs).        (exit 0; no error lines)
$ lake env lean scratchpad/T2131/audit_axioms.lean    # #print axioms of 25 declarations
LGraph.val_conj, lwSymm_conj_integral, LGraph.val_transpose, lwSymm_flip_measurePreserving, lwSymm_lwGm_flip,
lwSymm_transpose_integral, lwSymm_twist_integral, owxE_term_integral, owxE_graph_E, owxET1_counters, owxET1..4_ord,
lwSymm_{weight,oe1x,oe2x}_graph_E, lwSymm_{weight,oe1x,oe2x}_counters, lwSymm_hX_of_normal,
lwSymm_conj_literal_false, lwSymm_flipLit_ne : depends on axioms: [propext, Classical.choice, Quot.sound]
lwSymm_selector_edge, lwSymm_selector_pair : depends on axioms: [propext]
exit 0
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" RBM3D/Graph/LWSymm.lean | wc -l
0
$ git diff --name-only main...t/T2131
RBM3D/Graph/LWSymm.lean
$ (187 def/theorem names of LWSymm.lean grepped as declarations in every other RBM3D/**/*.lean)
clashes: 0
```
The only file changed is a sole writable file. No merged file or frozen signature is touched. `Test/Axioms.lean` is unchanged, and the module adds no `Prop`-valued `def`.

## 2. Statements against the ticket

Merged references used for comparison: `LWVocab.lean:115-122` (`SEdge.val`, `WEdge.val`), `LWWeightExp.lean:1316` (`owx_graph_E`), `LWEdgeExp.lean:1298` (`oe1x_graph_E`) and `LWGGExp.lean:1550` (`oe2x_graph_E`).

**Target 1 (S1): PASS.**
- `LGraph.conj` flips `σ` on solid edges and sends `m ↦ star m`. On a coloured waved edge it sends `⟨true,σ,x,y⟩ ↦ ⟨true,!σ,y,x⟩`. Black waved edges and dotted edges are unchanged.
- The auditor checked this by hand against `WEdge.val`. For σ=true, `star Sp(ℓx,ℓy)` is the red value of `⟨true,false,y,x⟩`. For σ=false, `star(star Sp(ℓy,ℓx)) = Sp(ℓy,ℓx)` is the blue value of `⟨true,true,y,x⟩`. So no hypothesis on `Sp` is needed.
- `LGraph.val_conj (D) (hS : ∀ i j, star (D.S i j) = D.S i j) : Γ.conj.val D ℓe = star (Γ.val D ℓe)`. The data is the same `D`. The only hypothesis is that `S` is real, which is the ticket's "e.g. `D.S` real".
- The ticket's reading "for `D.conj`" (that is, `Ḡ, M̄`) is false: the red edge already reads `star G`, so `D.conj` conjugates twice. The prover compiled a refutation, `lwSymm_conj_literal_false`.
- The ticket allowed "or prove the expectation identity directly". The prover did this as `lwSymm_conj_integral`, for any `M, Sp` with `S` real. `lwS` is proved real by `lwSymm_lwS_real`.

**Target 2 (S2): PASS.**
- `FineModel.lean:105-109` gives `Xentry = ω(i,j,true) + I·ω(i,j,false)`, so `b = false` is the imaginary part. The flip `lwSymmFlip` negates `b = false` (`lwSymmSgn b = if b then 1 else -1`).
- The ticket's literal `(if b then −1 else 1)` negates the real part. The prover compiled a refutation, `lwSymm_flipLit_ne`. The ticket itself asked to "check which value of `b` is the imaginary part".
- `lwSymm_flip_measurePreserving : MeasurePreserving (lwSymmFlipEquiv sz) seqP seqP` and `lwSymm_lwGm_flip : lwGm (flip ω) = (lwGm ω)ᵀ`.
- `lwSymm_transpose_integral (hM : Mᵀ = M) (hS : Sᵀ = S) (hSp : Spᵀ = Sp)` states `∫ Γ.transpose.val = ∫ Γ.val`. The hypotheses are exactly the ticket's.
- `LGraph.val_transpose` holds for any `D` (`Γᵀ.val D = Γ.val Dᵀ`).
- Integrability is not needed, because `MeasurePreserving.integral_comp'` holds for every function.

**Target 3 (S3): PASS.**
- `owxE_graph_E` is `owx_graph_E` with `(x : I)` replaced by `(x : E ⊕ I)` and `hx : p.1 = ⟨true,true,x,x⟩`. The hypotheses (`hG, hz, hu, hm0, hzm, hSp, hM`) are the same, the four-term shape is the same, and `ℓe` is fixed. The term constructors are `owxET1..4`.
- The new constructors are not ad hoc: `owxET{1..4}_inr` prove `owxET k … (Sum.inr x) = owxT k … x` by `rfl`.
- Counters: `owxET1_counters` and `owxET1..4_ord`, each `ord + 1` for any `x : E ⊕ I`.

**Target 4 (forms for `strat_local`): PASS.**
- **(a)** `lwSymm_weight_graph_E`: `x : E ⊕ I` with selector `hx : lwSymmTwistS c t p.1 = ⟨true,true,x,x⟩` gives a weight of either colour, internal or external.
- **(b)** `lwSymm_oe1x_graph_E` with `hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, inr x, v⟩` covers blue/red × out/in.
- **(c)** `lwSymm_oe2x_graph_E` with `hp1/hq1` twisted covers `GG`, `ḠḠ` and the transposed pairs.
- Every output is `lwSymmTwistG c t (merged term of the frame)`. Counters and `ord` of every output are in `lwSymm_{weight,oe1x,oe2x}_counters`. The `+0` case of `oe1xDs` is stated through the twisted `q.1`.
- One uniform shape with selector `(c,t)`, which `lwSymm_selector_edge`/`lwSymm_selector_pair` produce. `selector_pair` needs `q.σ = p.σ`: same-colour pairs only, as in the paper's `(Oe2x)`.
- Hypotheses beyond the merged ones:
  - `hM0 : ∀ a b, a ≠ b → M a b = 0`, which the ticket requires.
  - `hSpT : Spᵀ = Sp`, which comes from the ticket's S2 hypotheses. It is proved for `lwSplus` (`lwSymm_lwSplus_symm`, `‖m‖²u<1`).
  - `hX`/`hX1`/`hX2` (`p.1.circ = true → ∃` a `×`-dotted edge between the ends). This is vacuous for uncircled edges. For circled non-loop edges it is necessary: without `ℓ src ≠ ℓ dst`, `(G−M)` differs from `G` by `m δ`. It is discharged for every `LGraph.Normal` graph by `lwSymm_hX_of_normal` (merged `Normal` (iii), `LWVocab.lean:990`). It is covered by delta candidate T2131e.

**Structure and dependencies.**
- No new structure.
- Every `def` introduced is data: graph or edge maps, `lwSymmCj : ℂ →+* ℂ`, the flip, and the frames.
- Every dependency is a merged module: `LWVocab`, `LWStein`, `LWWeightExp`, `LWEdgeExp`, `LWGGExp`, `FineModel`, `IBPPoly`.
- There is no cycle: the module imports only merged files and is imported by none.
- The external input `GaussIBP sz` is discharged by the proved `gaussIBP` in every instance. No external hypothesis is open.

## 3. Compiled nonempty instances (all in `LWSymm.lean`, built above)
`grep -n "^example" RBM3D/Graph/LWSymm.lean | wc -l` returns `24`. Instance data is T2107's `lwWxInstSz = lwWxSizes 3 3 1 (1/2)` (`LWWeightExp.lean:1382`: d=3, L=3, W=1), `E=0`, `t=u=1/2`, `zt 0 (1/2)` with `lwWx_inst_im`. `GaussIBP` is the proved `gaussIBP` and every hypothesis is discharged.

| target | line | data / nondegeneracy |
|---|---|---|
| (1) `val_conj` | 2078 | `Fin 3` data (complex `G`, `M=i·1`, real symmetric `S`, non-symmetric complex `Sp`); graph with both colours, a circled weight of each colour, black and both coloured waved edges, a `×`-dotted edge, coeff `1+i`; `conj ≠ Γ` (2082) |
| (2) `transpose_integral` | 2102 | on `p2Graph` at labels `0 ≠ Pi.single 0 1`; `hMs, lwS_symm, hSpT` discharged; flip is not the identity (2119) |
| (3) `owxE_graph_E` | 2144 | `Ǧ_{aa}G_{ax}`, the weight at **external** `a = inl 0`; counters computed by `decide` (2153); `owxET1..4_ord` (2171-2180) |
| (4a) | 2196 / 2210 | red weight at external / internal vertex, `(c,t)=(true,false)`, `hM0`, `hSpT` discharged |
| (4b) | 2245 | **circled** red in-edge `(Ḡ−M)_{ax}`, `(c,t)=(true,true)`, `hX` discharged by a real `×`-dotted edge; DS list lengths `[1,2,2,1]` (2263) |
| (4c) | 2287 / 2317 | transposed blue pair `(false,true)` / red pair `(true,false)` |

None of the instances uses `N = 0`, an empty index, a `False` premise or a collapsed window. The `hX` premises are vacuous in 2287 and 2317 because those edges are uncircled. They are non-vacuous in 2245.

## 4. Paper-delta coverage
`grep -c T2131 docs/paper-deltas.md` returns `0`. The candidates proposed in the prove report (d) cover every Lean/ticket/paper difference found above:
- `T2131a`: sign of the flip.
- `T2131b`: `conj` uses the same `D`.
- `T2131c`: `WEdge.conj` swaps the ends.
- `T2131d`: `(Owx)` at any vertex of `E ⊕ I`.
- `T2131e`: circled edges via `hM0` + `×`-dotted `hX`.
- `T2131f`: `Spᵀ = Sp` hypothesis.

The single-selected-edge scope and the loop case `y₁ = x` are listed as open issues. They are outside the ticket's targets.

## 5. Observations (no verdict impact)
- For T2128: forms (b) and (c) need `hX`. Call `lwSymm_hX_of_normal`, which needs `Γ.Normal` and `p.1.src ≠ p.1.dst`, or select uncircled edges. Red outputs carry `star m` coefficients through the twist.
- Section (a) of the prove report states that two of the ticket's wordings are false (S1 `D.conj`, S2 sign). Both are compiled as refutations. The ticket had left both points open ("check which value of `b`", "or prove the expectation identity directly"), so no dispatcher sign-off is needed.

## Verdict
Target 1 PASS; Target 2 PASS; Target 3 PASS; Target 4 (a)(b)(c) PASS. **T2131: PASS.**
