Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct 11 13:03:17 UTC 2026

Section (a) length: 88 lines including this one (`wc -l`).
Sources read: ticket; `t/T2395:RBM3D/Probe/T2395Pins.lean` 55-100, 225-280; `Graph/LWSymm.lean` 79-575; `Graph/BAAtomic.lean` 40-160;
`Graph/BAVocab.lean` 34-180; `Graph/BAExpandW.lean` 60-215; `Graph/BAExpand.lean` 55-100; `Gauss/FineModel.lean` 80-125, 437.

### (i) Exponent table (no scaling exponent enters; the constants are the hypotheses and the data constraints)

| item | value / statement | constraint | slack / status |
|---|---|---|---|
| twist `(c,t)` | `c`: `σ` of solid and `M`-edges flips, `S^±` waved ends swap+flip, coeff conjugated; `t`: ends swap (all edge kinds) | commute, involutive | probe 70-90 verbatim; `Γ.twist` = `lwSymmTwistG` (`LWSymm:171`) on `toLGraph` + `psi.map`, `mdot.map` |
| `BAtwistInv` | normal, `nExt`, `nLoops`, `nPairs` kept | true: `Normal` = (dotted `eq=false`) ∧ (solid `circ=true`); `lwSymmTwistG_dotted` (`:192`), `lwSymmTwistS_circ` (`:1230`) | `atom` is unchanged (proof of `ba_twist_counters`: `atomAdj`, `adj` unchanged), `sameAtom` symmetric (`BAAtomic_sameAtom_comm`, `BAAtomic:149`); `nShare`/`pairsAux` are symmetric in the two ends of each edge (sum over `[src,dst]`, filter length over `[src',dst']`) |
| `H_t` data | `H = g0 Ψ + √t X`, `z = E + (1-t) m` (`ztOf`), `G = (H - z)⁻¹` (`Gres`, `Ring.inverse`) | none for the twist | identity is algebraic: no invertibility, no `Im z > 0` used |
| `D = BAlwData` | `G`, `M = Mres(g0 Ψ, E, m)`, `S = t·svarF d L W 0`, `Sp = S·BAlwW`, `gPsi = g0 Ψ` | needed: `star S = S`, `Mᵀ = M`, `Sᵀ = S`, `Spᵀ = Sp`, `star gPsi = gPsi`, `gPsiᵀ = gPsi` | all five hold, see rows below |
| `Ψ` real, symmetric | `PsiI = (PsiB ⊗ 1).submatrix`, `PsiB` entries `0/1` (`Adj`: `zdistD(x-y)=1`) | `g0 ∈ ℝ` | `PsiB_isHermitian` (`BlockAnderson:55`), `PsiI_isHermitian` (`:65`) give `Ψᴴ = Ψ`; reality (entries `ite 1 0` times `1_{k=k'}`) and `Ψᵀ = Ψ` are new (~20 lines; `BAExpandW_PsiI_transpose` is `private`, `BAExpandW:180`) |
| `M` symmetric | `baM_symm` (`BAExpandW:187`), unconditional | none | proved, public |
| `S` real, symmetric | `star (t·svarF) = t·svarF` (`t ∈ ℝ`); `svarF_comm` (`FineModel:54`) | none | `t` real, no sign needed |
| `Sp` symmetric (**4th hypothesis `hSp`; ticket lists only `hSr, hM, hS`**) | `Sp = S·W`, `W = Ring.inverse(1 - M⁺S)`, `M⁺_{xy} = M_{xy}M_{yx}` symmetric | `Spᵀ = Ring.inverse(1 - S M⁺)·S` (transpose of `Ring.inverse`, `Matrix.transpose_nonsing_inv` is used at `LWSymm:402`) | push-through `S·(1-AS')⁻¹`: for `A=M⁺, B=S`: `B·Ring.inverse(1-AB) = Ring.inverse(1-BA)·B`. Unit case `(1-BA)⁻¹ = 1 + B(1-AB)⁻¹A`; nonunit case both sides `0` (`1-AB` unit iff `1-BA` unit). Unconditional (no `BASelf`, no `t<1`) |
| flip law | `flipF ω c = lwSymmSgn c.2.2 · ω c` (`LWSymm:369`) negates imaginary coordinates; `Xmat(flipF ω) = (Xmat ω)ᵀ` (`:397`); `Hflow(flipF ω) = (Hflow ω)ᵀ` (`Hflow = √u • Xmat`, `FineModel:437`) | `PF d L W 0` invariant | Gaussians `gaussianReal 0 (gvarF ·)` are symmetric (`gaussianReal_map_neg`); **`lwSymm_flip_measurePreserving` (`:441`) is on `Sizes.seqP`, not on `PF`**: one-size port with `Measure.infinitePi_map_pi` over `CoordF`, `Sizes.seqGvar → gvarF` (~35 lines) |
| `G(flip ω) = G(ω)ᵀ` | `Gres Hᵀ z true = (Gres H z true)ᵀ` (`lwSymm_Gres_transpose :402`) with `H = g0Ψ + Hflow`, `Ψᵀ = Ψ` | none | unconditional |
| `BASelf d L g0 Em m` | `0 < Im m ∧ m = L^{-d} tr(g0 Ψ_B - Em - m)⁻¹` (`MFixedPoint:193`) | statement hypothesis only | **not used by the proof of `BAtwistIntegral`** (algebra + flip invariance only) |
| `0 ≤ t < 1`, `3 ≤ L` | statement hypotheses | | not used by the proof either; no smallness of `g0` (C1) |
| bridge `PF` ↔ `seqP` | `lwWx_integral` (`LWWeightExp:331`) needs `F` continuous (needs `Im z_t>0`: `BASelf`, `t<1`) | | **avoided**: direct one-size flip needs no continuity and no measurability of the integrand (`MeasurePreserving.integral_comp'`, `integral_conj`) |

Why `lwSymm_twist_integral` (`:558`) is not applicable as a black box at BA (finding): it is stated for `LGraph.val`, `lwSampleData sz n z u M S Sp`
and `Sizes.seqP sz`; `BAGraph.val` has the extra `Ψ`- and `M`-dotted factors (`BAGraph.term`, `BAVocab:72`), the law is `PF d L W 0` on `Ω d L W`.
Its ingredients are reused (all public): `lwSymmTwistG_val`-type proof, `lwSymm_term_conj` (`:232`), `lwSymm_term_transpose` (`:246`), `lwSymm_Xmat_flip`,
`lwSymm_Gres_transpose`, `lwSymm_integral_cj` (`:551`), `lwSymmTwistS_circ`, `lwSymmTwistG_adj/_solid/_dotted`. Paper-delta candidate `T2425a`: none in statements
(the three targets are the probe pins); the proof route differs from the ticket's sentence "from `lwSymm_twist_integral`" (it is the twin, not a call).

**Section map `LWSymm` → `BASymm1`** (file:line → planned declaration; `BASymm1_` = private helper stem):

| `LWSymm` | planned BA declaration |
|---|---|
| 86-112 `SEdge/WEdge/LGraph.conj/transpose`, 116-157 involutions | reused; none needed (`twist_invol` not a target) |
| 164-199 `lwSymmCj`, `lwSymmTwistG` + `_solid/_dotted/_coeff` | reused; `BAMEdge.twist`, `BAPsiEdge.twist`, `BAGraph.twist` (probe 70-90, verbatim) |
| 205-266 value lemmas on `SEdge/WEdge/DEdge` | reused for the `LGraph` factor; new `BASymm1_medge_val`, `BASymm1_psiedge_val` (edge factor of the twist) |
| 271-286 `lwSymmDataTr`, `lwSymmTwistG_val` | new `BASymm1_dataTr (D : BALData) (t)` (`D.toLData.transpose`, `gPsiᵀ`), `BAGraph.BASymm1_val_twist` (needs `star S = S`, `star gPsi = gPsi`) |
| 295-351 counters | `ba_twist_counters` (probe, verbatim) + `BAGraph.twist_atom`, then `BAtwistInv` (new: `Normal`, `nExt`, `nLoops` by `List.countP_map`, `nPairs` by induction on `solid`) |
| 366-466 flip, 441 measure-preserving | reuse `lwSymmFlipF`, `lwSymm_Xmat_flip`, `lwSymm_Gres_transpose`; new `BASymm1_flip_measurePreserving` on `PF d L W 0`, `BASymm1_data_flip` (`BAlwData(flipF ω) = (BAlwData ω)` transposed) |
| 471-519 negations | not needed |
| 527-575 expectation | `BAtwistIntegral d` proved: `BASymm1_integral_flip`, then `lwSymm_integral_cj` at `PF` |

**Predicted lines** (code, without module doc): probe pins ~45; `BAtwistInv` ~100; `Ψ` real/symm, `Sp` symmetric, data flip ~90; one-size flip measure ~50; BA `val_twist` ~110;
integral ~40; instances ~70; header/doc ~60. Total ~565 (ticket estimate 900 landed, stop line 2,000: slack ≥ 1,400).

### (ii) One concrete nondegenerate instance

`d = 3`, `L = 4`, `W = 2` (`N = (W L)^d = 512`), flow point of `(L, g) = (4, 10)` (`BA/CouplingWindow.lean:861-864`: `t0P, EP, m0P, g0P`; `flowP_data : 0 < t0P ∧ t0P < 1 ∧ BASelf 3 4 g0P EP m0P`, `:869`, namespace `RBM.BA.CouplingWindowInst`).
Graph (`E = Fin 2`, `I = Fin 1`; vertices `v0, v1, u`): solid `G_{v0 u}` (uncircled), `Ḡ_{u v1}`; waved `S⁺_{v0 v1}` (coloured) and `S_{v0 u}` (black); `×`-dotted `v0 v1`;
`M`-edge `v0 — u` (`σ = true`, joins one atom `{v0,u}`); `Ψ`-edge `u — v1`; coeff `1 + 0.5 i`. Labels `ℓe v0` = block `(0,0,0)` offset `0`, `ℓe v1` = block `(1,0,0)` offset `0` (adjacent blocks, same offset: `Ψ` and `M` kron-structured).
Script: numerics only (no Lean), reads `PsiB` as the `Z_4^3` adjacency (`Adj`), `S = t·W^{-d}·1([x]=[y])` (`SB d L 0 = 1`, `EMn2BA_SB_zero`, `BA/EMn2BA.lean:77`), `gvarF` variances (`FineModel:89`), `Xentry` (`FineModel:105`).

```
$ python3 <scratchpad>/T2425/inst.py     # scratchpad = /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/60e5425b-ae97-4201-b2dc-fc981af93073/scratchpad
Im zS=0.938031 Im mS=0.261969  t0=0.218307 E=-0.000000 g0=4.672337 m0=0.000000+0.560680i
BASelf: Im m0 = 0.560680 > 0 ; |m0 - L^-3 tr(g0 Psi-E-m0)^-1| = 3.33e-16 ; 0<t0<1: True
N=512  Psi real sym: True True | M sym: 2.2e-15 | S real sym | Sp sym: 2.87e-15 (push-through)
IsUnit(1 - M+ S): min singular value 1.000
M offdiag max |M_xy| (x!=y) = 0.5546, Psi entries nonzero: 3072
G(flip w) = G(w)^T : max err 1.02e-14
base val = -4.887097e-08-7.993573e-09i
twist (c=0,t=0): rel.err of val(twist) vs cj(val(D^t)) = 0.00e+00
   pathwise vs D(flip^t omega), rel.err: 0.00e+00
twist (c=0,t=1): rel.err of val(twist) vs cj(val(D^t)) = 0.00e+00
   pathwise vs D(flip^t omega), rel.err: 9.47e-14
twist (c=1,t=0): rel.err of val(twist) vs cj(val(D^t)) = 0.00e+00
   pathwise vs D(flip^t omega), rel.err: 0.00e+00
twist (c=1,t=1): rel.err of val(twist) vs cj(val(D^t)) = 0.00e+00
   pathwise vs D(flip^t omega), rel.err: 9.47e-14
```
Reading: every hypothesis of `BAtwistIntegral` holds at once (`BASelf` residual `3e-16`, `0 < t0 = 0.2183 < 1`, `3 ≤ 4`, `g0 = 4.67 ≠ 0`, `M` non-diagonal), and the pathwise identity
`(Γ.twist c t).val (D ω) = cj^c (Γ.val (D (flip^t ω)))` of the three-line proof of the integral holds for all four twists. Not checked by the script: `E = 0` is a
numerical coincidence of the symmetric flow point (`Re z_S = Re m_S = 0`), no hypothesis requires `E ≠ 0`. In Lean the instance uses the compiled `flowP_data` (needs `import RBM3D.BA.CouplingWindow`,
which imports only `BA.MFixedPoint`; no cycle with `Graph`). Fallback if that import is unwanted: `RBM.Graph.BAExpandInst.baSelf_zero : BASelf 3 3 0 0 I` (`BAExpand.lean:865`, `W = 1`, `t = 1/2`),
where `g0 = 0` and `M = i·1` are degenerate; then the `M`/`Ψ`-edge values vanish between distinct vertices, so `flowP` is the recommended instance.
`BAtwistInv` instance: the same graph with solid edges circled (normal; `eq = false` dotted), `E = Fin 2`, `I = Fin 1`; `Normal` has a `Decidable` instance (`BAAtomic`), `nLoops`, `nPairs`, `nExt` are `ℕ`-valued defs evaluated by `decide`/`rfl` at the explicit graph.
External hypothesis: none (BASelf is a proved base, discharged by `flowP_data`; no external input).

### Verdicts
1. twist definitions, `twist_atomAdj`, `ba_twist_counters` (probe verbatim): **PASS** (statements true; proofs in the probe use only merged `lwSymmTwistG_*`, `BAGraph.atomAdj/adj`).
2. `BAtwistInv`: **PASS** (true; needs `BAAtomic_sameAtom_comm` and `(Γ.twist c t).atom = Γ.atom` (the inline `hA` of `ba_twist_counters`); no missing input).
3. `BAtwistIntegral d`: **PASS**, with two findings: (a) `hSp` (fourth hypothesis) is needed and is discharged by push-through; (b) route is the twin, not a call of `lwSymm_twist_integral` (`seqP`/`LGraph.val` mismatch); one-size flip invariance of `PF` is new. `BASelf`, `t<1` unused.
4. Instances: **PASS** at the `flowP` datum (`d = 3, L = 4, W = 2`); no `N = 0`, no collapsed window.
5. C1 (`BASelf`, `0 ≤ t < 1` only): **PASS**. 6. Registry none; pre-check `import RBM3D` + `#assert_rbm_axioms`.
Overall: **PASS**

## (b) Script output — Sun Oct 11 13:19:26 UTC 2026

Branch `t/T2425`, commit `ef3f4a4`, one file.  `RBM3D.lean` is not edited (the hub adds the import at merge, CLAUDE.md §3 (A) step 4); the pre-check imports `RBM3D` and the module together.

```
$ wc -l RBM3D/Graph/BASymm1.lean; git log --oneline -1; git diff --stat main...t/T2425
     475 RBM3D/Graph/BASymm1.lean
ef3f4a4 T2425: BASymm1 twists of a BA graph, BAtwistInv, BAtwistIntegral, instances
 RBM3D/Graph/BASymm1.lean | 475 +++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 475 insertions(+)

$ section map (LWSymm line -> BASymm1 line; twin or reused ingredient)
LWSymm:171   lwSymmTwistG                   -> BASymm1:71   BAGraph.twist
LWSymm:328   lwSymmTwistG_adj               -> BASymm1:73   BAGraph.twist_atomAdj
LWSymm:328   lwSymmTwistG_adj               -> BASymm1:101  BAGraph.BASymm1_twist_atom
LWSymm:333   lwSymmTwistG_counters          -> BASymm1:83   ba_twist_counters
LWSymm:1230  lwSymmTwistS_circ              -> BASymm1:175  baTwistInv_holds
LWSymm:271   lwSymmDataTr                   -> BASymm1:208  BASymm1_dataTr
LWSymm:232   lwSymm_term_conj               -> BASymm1:226  BASymm1_term_twist_L
LWSymm:246   lwSymm_term_transpose          -> BASymm1:245  BAGraph.BASymm1_term_twist
LWSymm:274   lwSymmTwistG_val               -> BASymm1:261  BAGraph.BASymm1_val_twist
LWSymm:397   lwSymm_Xmat_flip               -> BASymm1:327  BASymm1_H_flip
LWSymm:424   lwSymm_data_flip               -> BASymm1:332  BASymm1_dataTr_flip
LWSymm:441   lwSymm_flip_measurePreserving  -> BASymm1:370  BASymm1_flip_measurePreserving
LWSymm:558   lwSymm_twist_integral          -> BASymm1:407  baTwistIntegral_holds

$ verbatim pins against the T2395 probe (git show t/T2395:RBM3D/Probe/T2395Pins.lean > probe.lean)
diff probe 71-104 vs RBM3D/Graph/BASymm1.lean 65-98: exit 0
diff probe 272-273 (BAtwistInv) vs RBM3D/Graph/BASymm1.lean 171-172: exit 0
diff probe 234-238 (BAtwistIntegral) vs RBM3D/Graph/BASymm1.lean 399-403: exit 0

$ lake build RBM3D.Graph.BASymm1 > build.out 2>&1; tail -1 build.out; grep -c "BASymm1.lean" build.out
exit 0
Build completed successfully (3810 jobs).
warnings/errors in BASymm1.lean: 0

$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Graph/BASymm1.lean
(exit 1; 1 = no match)

$ lake env lean axioms.lean  (#print axioms of the targets, helpers and instance lemmas)
BAGraph.twist_atomAdj: [propext, Classical.choice, Quot.sound]
ba_twist_counters: [propext, Classical.choice, Quot.sound]
BAGraph.BASymm1_twist_atom: [propext, Classical.choice, Quot.sound]
baTwistInv_holds: [propext, Classical.choice, Quot.sound]
BAGraph.BASymm1_val_twist: [propext, Classical.choice, Quot.sound]
BASymm1_dataTr_flip: [propext, Classical.choice, Quot.sound]
BASymm1_flip_measurePreserving: [propext, Classical.choice, Quot.sound]
baTwistIntegral_holds: [propext, Classical.choice, Quot.sound]
BASymm1Inst.G0_normal: [propext, Classical.choice, Quot.sound]
BASymm1Inst.G0_counts: [propext, Classical.choice, Quot.sound]

$ lake env lean docs/tickets/checks/T2425-check.lean > /dev/null; echo $?
exit 0

$ lake env lean precheck.lean   (import RBM3D; import RBM3D.Graph.BASymm1; #assert_rbm_axioms)
exit 0
axiom audit: 11939 theorems, 3688 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.

$ python3 -I stmt.py (statements extracted by script)
Graph/BASymm1.lean:73
theorem BAGraph.twist_atomAdj (c t : Bool) (Γ : BAGraph E I) : (Γ.twist c t).atomAdj = Γ.atomAdj := by ...
Graph/BASymm1.lean:83
theorem ba_twist_counters (c t : Bool) (Γ : BAGraph E I) : (Γ.twist c t).counters = Γ.counters := by ...
Graph/BASymm1.lean:171
def BAtwistInv : Prop := ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (c t : Bool) (Γ : BAGraph E I),
  (Γ.Normal → (Γ.twist c t).Normal) ∧ (Γ.twist c t).nExt = Γ.nExt ∧ (Γ.twist c t).nLoops = Γ.nLoops ∧ (Γ.twist c t).nPairs = Γ.nPairs
Graph/BASymm1.lean:175
theorem baTwistInv_holds : BAtwistInv := by ...
Graph/BASymm1.lean:399
def BAtwistIntegral (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 →
    ∀ {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (c t' : Bool) (Γ : BAGraph Ex Ix) (ℓe : Ex → Idx d L W),
      ∫ ω, (Γ.twist c t').val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
        (if c then (star : ℂ → ℂ) else id) (∫ ω, Γ.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0))
Graph/BASymm1.lean:407
theorem baTwistIntegral_holds (d : ℕ) : BAtwistIntegral d := by ...
$ grep -rnE "BASymm1|BAtwistInv|BAtwistIntegral|baTwistInv|baTwistIntegral|ba_twist_counters|twist_atomAdj|BAMEdge.twist|BAPsiEdge.twist|BAGraph.twist" RBM3D RBM3D.lean | grep -v Graph/BASymm1.lean | wc -l   (name clash)
       0
```

The compiled instances (`namespace BASymm1Inst` of the file, docstrings stripped by script; they are part of the build above):

```
namespace BASymm1Inst
def G0 : BAGraph (Fin 2) (Fin 3) where
  solid := [⟨true, true, Sum.inl 0, Sum.inr 0⟩, ⟨false, true, Sum.inr 1, Sum.inl 1⟩, ⟨true, true, Sum.inl 1, Sum.inr 2⟩]
  waved := [⟨true, true, Sum.inl 0, Sum.inl 1⟩, ⟨false, true, Sum.inl 0, Sum.inr 0⟩]
  dotted := [⟨false, Sum.inl 0, Sum.inl 1⟩]
  coeff := 1 + (1 / 2 : ℂ) * Complex.I
  psi := [⟨Sum.inl 1, Sum.inr 2⟩]
  mdot := [⟨true, Sum.inr 0, Sum.inr 1⟩]
theorem G0_normal : G0.Normal := ⟨by decide, by decide⟩
theorem G0_counts : G0.nExt = 2 ∧ G0.nLoops = 1 ∧ G0.nPairs = 1 := by decide
def ℓ0 : Fin 2 → Idx 3 4 2 := fun a => (splitEquiv 3 4 2).symm (if a = 0 then (0, 0) else (Pi.single 0 1, 0))
example : (G0.twist true true).mdot.map (fun e => (e.σ, e.x, e.y)) = [(false, Sum.inr 1, Sum.inr 0)] ∧
    (G0.twist true true).psi.map (fun e => (e.x, e.y)) = [(Sum.inr 2, Sum.inl 1)] := by
  constructor <;> rfl
example : (G0.twist true true).atomAdj = G0.atomAdj ∧ (G0.twist true true).counters = G0.counters :=
  ⟨BAGraph.twist_atomAdj true true G0, ba_twist_counters true true G0⟩
example : (G0.twist true true).Normal ∧ (G0.twist true true).nExt = 2 ∧ (G0.twist true true).nLoops = 1 ∧
    (G0.twist true true).nPairs = 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := baTwistInv_holds true true G0
  obtain ⟨c1, c2, c3⟩ := G0_counts
  exact ⟨h1 G0_normal, h2.trans c1, h3.trans c2, h4.trans c3⟩
open RBM.BA.CouplingWindowInst in
example (c t' : Bool) :
    ∫ ω, (G0.twist c t').val (BAlwData 3 4 2 g0P EP t0P m0P ω) ℓ0 ∂(PF 3 4 2 0) =
      (if c then (star : ℂ → ℂ) else id) (∫ ω, G0.val (BAlwData 3 4 2 g0P EP t0P m0P ω) ℓ0 ∂(PF 3 4 2 0)) :=
  baTwistIntegral_holds 3 4 2 (by norm_num) g0P EP t0P m0P flowP_data.2.2 flowP_data.1.le flowP_data.2.1 c t' G0 ℓ0
end BASymm1Inst
```

Narrative:
- Targets 1-3 are in one file of 475 lines (stop line 2,000).  The pins (probe 71-104), `BAtwistInv` (probe 272) and `BAtwistIntegral` (probe 234) are identical to the probe (the three `diff`s, exit 0);
  `baTwistInv_holds : BAtwistInv` and `baTwistIntegral_holds : ∀ d, BAtwistIntegral d` are proved.  The ten printed declarations and (by the `#assert_rbm_axioms` pre-check) every `RBM` declaration use only the standard three axioms.
- Route of the integral, as in (a): the twin of `LWSymm` §1-§3, not a call of `lwSymm_twist_integral` (`LGraph.val`, `lwSampleData`, `Sizes.seqP` there; `BAGraph.val`, `BAlwData`, `PF d L W 0` here).
  Pathwise `(Γ.twist c t).val D = (conj if c) (Γ.val (D transposed if t))` (`BAGraph.BASymm1_val_twist`; needs `star S = S`, `star gPsi = gPsi`: `BASymm1_data_real`); `D(ω)` transposed is `D(flip ω)`
  (`BASymm1_dataTr_flip`); `PF d L W g` is flip invariant (`BASymm1_flip_measurePreserving`, one-size port of `lwSymm_flip_measurePreserving`); then `MeasurePreserving.integral_comp'`, `lwSymm_integral_cj`.
- Finding of (a) confirmed: `S⁺ᵀ = S⁺` is needed (`S⁺ = S·BAlwW` in `BAlwData`): `BASymm1_Sp_symm`, from the push-through identity `BASymm1_pushThrough` (`b (1 - ab)⁻¹ = (1 - ba)⁻¹ b` for `Ring.inverse` in any ring),
  `Sᵀ = S` (`svarF_comm`), `M⁺ᵀ = M⁺`.  `Ψ` symmetric is the `private` `BAExpandW_PsiI_transpose`, read by `open private ... from RBM3D.Graph.BAExpandW` (as `BAExpandId.lean` does); `Ψ` real follows from
  `PsiI_isHermitian` and the symmetry (not "new, ~20 lines" as in (a)); `M` symmetric is `baM_symm` (used in `BASymm1_dataTr_flip`; the `M`-edge value of a twist needs no symmetry).
- `BASelf`, `0 ≤ t`, `t < 1`, `3 ≤ L` are hypotheses of the statement (verbatim) and unused by the proof (C1); `baTwistInv_holds` is unconditional.
- Instance graph `G0 : BAGraph (Fin 2) (Fin 3)` (not the `I = Fin 1` graph of (a)(ii), a numeric check of the pathwise identity; `d = 3, L = 4, W = 2` and `flowP` are the same): external `v0, v1`, internal `u, w, x`;
  `M`-edge `u—w` (internal atom `{u,w}`), `Ψ`-edge `v1—x`, solid edges between atoms and one inside the atom `{v1,x}`, coloured and black waved edges, a `×`-dotted edge, coefficient `1 + i/2`;
  `nExt = 2`, `nLoops = 1`, `nPairs = 1` by `decide`.  `BAtwistIntegral` is applied with `flowP_data` (`BASelf`, `0 < t₀ < 1`, proved in `BA/CouplingWindow.lean`); its integrals are not evaluated (statement level).
- The file imports `RBM3D.BA.CouplingWindow` (imports `BA.MFixedPoint` only; no cycle) for the instances.  No port from RBM1D or RBM2D.

## (c) Verified Mathlib names (each `#check`ed in this worktree)

`Matrix.transpose_nonsing_inv`, `Matrix.nonsing_inv_eq_ringInverse`, `Matrix.transpose_smul`, `Matrix.IsHermitian.apply`, `Ring.inverse_mul_cancel`, `Ring.mul_inverse_cancel`, `Ring.inverse_non_unit`,
`List.countP_map`, `List.countP_congr`, `List.Perm.filter`, `List.Perm.length_eq`, `List.Perm.map`, `List.Perm.sum_eq`, `List.Perm.swap`, `List.map_congr_left`, `map_list_prod`,
`Measure.infinitePi_map_pi`, `gaussianReal_map_neg`, `Measure.map_id`, `MeasurePreserving.integral_comp'`, `Measurable.of_eval`.
Verified absent: `isUnit_one_sub_mul_comm` (`BASymm1_pushThrough` repeats the unit transfer `IsUnit (1 - a b) → IsUnit (1 - b a)` of `Mathlib/Algebra/Algebra/Spectrum/Basic.lean:248`, `unit_mem_mul_comm`).

## (d) Open issues and paper-delta candidates

- `T2425a` (no statement delta): the three targets are the probe pins; the proof route differs from the ticket sentence "from `lwSymm_twist_integral`" (a twin, not a call).  `BASymm1_flip_measurePreserving` and `BASymm1_pushThrough` are reusable by the other BA files.
- `RBM3D.lean` import line: left to the hub; the ticket lists `RBM3D.lean` among the writable files.  A downstream file that imports `BASymm1` inherits `RBM3D.BA.CouplingWindow`.
