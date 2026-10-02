# T2002 port map: RBM2D `c9a24cf` -> RBM3D, stochastic side (design report, ticket T2002)

Generated Fri Oct  2 23:01:40 UTC 2026 by the scripts of part J. RBM2D is read at commit `c9a24cf` (the ticket's commit). RBM2D `HEAD` was `81fca44` at generation time (its Lean tree differs from that of `0c1330a`); commit `99d6fe0` ("T2274: merge dead-code deletion (82 modules removed, 328 files trimmed)") is RBM2D's own dead-code deletion, `git diff --shortstat c9a24cf 0c1330a -- RBM2D RBM2D.lean`: 416 files changed, 2393 insertions(+), 62551 deletions(-). The column "kept" is the line count at `0c1330a` (`-1` = file deleted), i.e. the part of each file that the final d=2 proof uses.
RBM3D is read at the branch point `3c11d7b` of `main` (the tree of `t/T2002`); `main` has since moved to `709c5c7`, and the only Lean changes are the new file `RBM3D/Defs/SemicircleIntegral.lean` of T2005 (`709c5c7`; one public theorem, no definition: prove report b.7) and its import line in `RBM3D.lean`, so the inventory of definitions A.1 is unchanged. Line counts are `wc -l` of `git show <commit>:<file>`; "reachable" is the transitive `import` closure of `RBM2D/Main/Endpoints.lean` and `RBM2D/Main/BUnivHolds.lean` at `c9a24cf`.

## A. Inventories (ticket item 1)

### A.1 RBM3D on `main` (`3c11d7b`): every public definition of `Defs/*`, `Gauss/*`, `Loop/GLoop.lean`, `Analysis/Resolvent.lean`, elaborated signature (script `Inv.lean`, output verbatim, `module:line kind name : type`)

```
RBM3D.Defs.Block:37 def RBM.sbKernel : (d L : ℕ) → ℝ → RBM.Zd d L → ℂ
RBM3D.Defs.Block:43 def RBM.SB : (d L : ℕ) → ℝ → Matrix (RBM.Zd d L) (RBM.Zd d L) ℂ
RBM3D.Defs.Block:73 def RBM.sbKernelR : (d L : ℕ) → ℝ → RBM.Zd d L → ℝ
RBM3D.Defs.Convolution:121 def RBM.powW : ℕ → ℕ → ℝ
RBM3D.Defs.Convolution:141 def RBM.κ₀ : ℝ
RBM3D.Defs.Convolution:220 def RBM.convC : ℕ → ℝ
RBM3D.Defs.Domination:49 def RBM.UnifDetDom : {U : ℕ → Type u_1} → ((N : ℕ) → U N → ℝ) → ((N : ℕ) → U N → ℝ) → Prop
RBM3D.Defs.Domination:55 def RBM.DetDom : (ℕ → ℝ) → (ℕ → ℝ) → Prop
RBM3D.Defs.Domination:60 def RBM.«term_≺_» : TrailingParserDescr
RBM3D.Defs.Lattice:24 def RBM.zdist : (L : ℕ) → ZMod L → ℕ
RBM3D.Defs.Lattice:61 def RBM.Zd : ℕ → ℕ → Type
RBM3D.Defs.Lattice:70 def RBM.zdistD : (d L : ℕ) → RBM.Zd d L → ℕ
RBM3D.Defs.Lattice:73 def RBM.torusDiam : ℕ → (L : ℕ) → [NeZero L] → ℕ
RBM3D.Defs.Lattice:107 def RBM.Adj : (d L : ℕ) → RBM.Zd d L → RBM.Zd d L → Prop
RBM3D.Defs.Neighbours:75 def RBM.unitVec : (d L : ℕ) → Fin d × Bool → RBM.Zd d L
RBM3D.Defs.Neighbours:163 def RBM.instDecidableAdj : {d L : ℕ} → (x y : RBM.Zd d L) → Decidable (RBM.Adj d L x y)
RBM3D.Defs.Params:31 def RBM.ellT : ℕ → ℝ → ℝ → ℝ
RBM3D.Defs.Params:35 def RBM.Bparam : ℕ → ℕ → ℝ → ℝ → ℕ → ℝ
RBM3D.Defs.RadialSum:96 def RBM.radC : ℝ → ℝ
RBM3D.Defs.RadialSum:270 def RBM.expC : ℕ → ℝ → ℝ
RBM3D.Defs.RadialSum:355 def RBM.ballC : ℕ → ℝ
RBM3D.Defs.Semicircle:36 def RBM.mE : ℝ → ℂ
RBM3D.Defs.Semicircle:84 def RBM.mSigma : ℝ → Bool → ℂ
RBM3D.Defs.Semicircle:101 def RBM.mscDisc : ℂ → ℂ
RBM3D.Defs.Semicircle:109 def RBM.mscRoot₁ : ℂ → ℂ
RBM3D.Defs.Semicircle:112 def RBM.mscRoot₂ : ℂ → ℂ
RBM3D.Defs.Semicircle:114 def RBM.msc : ℂ → ℂ
RBM3D.Defs.Semicircle:178 def RBM.zt : ℝ → ℝ → ℂ
RBM3D.Defs.Semicircle:189 def RBM.lemE : ℂ → ℝ
RBM3D.Defs.Semicircle:192 def RBM.lemT : ℂ → ℝ
RBM3D.Defs.Shells:68 def RBM.sphereCard : ℕ → (L : ℕ) → [NeZero L] → ℕ → ℕ
RBM3D.Defs.StochDom:75 def RBM.badSet : {Ω : Type u_1} → {U : ℕ → Type u_2} → ((N : ℕ) → U N → Ω → ℝ) → ((N : ℕ) → U N → Ω → ℝ) → ℝ → ℕ → Set Ω
RBM3D.Defs.StochDom:79 def RBM.StochDom : {Ω : Type u_1} →  [inst : MeasurableSpace Ω] →   MeasureTheory.Measure Ω → {U : ℕ → Type u_2} → ((N : ℕ) → U N → Ω → ℝ) → ((N : ℕ) → U N → Ω → ℝ) → Prop
RBM3D.Defs.StochDom:84 def RBM.NormStochDom : {Ω : Type u_1} →  [inst : MeasurableSpace Ω] →   MeasureTheory.Measure Ω →    {U : ℕ → Type u_2} → {E : Type u_3} → [Norm E] → ((N : ℕ) → U N → Ω → E) → ((N : ℕ) → U N → Ω → ℝ) → Prop
RBM3D.Defs.StochDom:88 def RBM.HighProb : {Ω : Type u_1} → [inst : MeasurableSpace Ω] → MeasureTheory.Measure Ω → (ℕ → Set Ω) → Prop
RBM3D.Defs.StochDom:92 def RBM.HighProbIn : {Ω : Type u_1} → [inst : MeasurableSpace Ω] → MeasureTheory.Measure Ω → (ℕ → Set Ω) → (ℕ → Set Ω) → Prop
RBM3D.Defs.Tail:43 def RBM.BparamR : ℕ → ℕ → ℝ → ℝ → ℝ → ℝ
RBM3D.Defs.Tail:47 def RBM.tailT : ℕ → ℕ → ℝ → ℝ → ℝ → ℝ
RBM3D.Defs.Tail:51 def RBM.tailW : ℕ → ℕ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
RBM3D.Gauss.Domination:65 def RBM.Gauss.MomentDom : {Ω : Type u_1} →  [inst : MeasurableSpace Ω] →   MeasureTheory.Measure Ω → {U : ℕ → Type u_2} → ((N : ℕ) → U N → Ω → ℝ) → ((N : ℕ) → U N → ℝ) → Prop
RBM3D.Gauss.Domination:139 def RBM.Gauss.netSize : ℝ → ℕ → ℕ
RBM3D.Gauss.Domination:151 def RBM.Gauss.netPt : ℝ → (A : ℝ) → (N : ℕ) → Fin (RBM.Gauss.netSize A N + 1) → ℝ
RBM3D.Gauss.Model:58 def RBM.Gauss.Vtx : ℕ → ℕ → ℕ → Type
RBM3D.Gauss.Model:62 def RBM.Gauss.svar : (d L W : ℕ) → ℝ → RBM.Gauss.Vtx d L W → RBM.Gauss.Vtx d L W → ℝ
RBM3D.Gauss.Model:77 def RBM.Gauss.vkey : (d L W : ℕ) → [NeZero L] → RBM.Gauss.Vtx d L W → ℕ
RBM3D.Gauss.Model:84 def RBM.Gauss.Coord : ℕ → ℕ → ℕ → Type
RBM3D.Gauss.Model:89 def RBM.Gauss.Omega : ℕ → ℕ → ℕ → Type
RBM3D.Gauss.Model:92 def RBM.Gauss.gvar : (d L W : ℕ) → ℝ → RBM.Gauss.Coord d L W → NNReal
RBM3D.Gauss.Model:100 def RBM.Gauss.P : (d L W : ℕ) → ℝ → [NeZero L] → MeasureTheory.Measure (RBM.Gauss.Omega d L W)
RBM3D.Gauss.Model:109 def RBM.Gauss.Hmat : (d L W : ℕ) → [NeZero L] → RBM.Gauss.Omega d L W → Matrix (RBM.Gauss.Vtx d L W) (RBM.Gauss.Vtx d L W) ℂ
RBM3D.Gauss.SteinMatrix:69 def RBM.Gauss.upd : {ι : Type u_1} → [DecidableEq ι] → ι → (ι → ℝ) × ℝ → ι → ℝ
RBM3D.Loop.GLoop:49 def RBM.Gauss.Eblk : (d L W : ℕ) → RBM.Zd d L → Matrix (RBM.Gauss.Vtx d L W) (RBM.Gauss.Vtx d L W) ℂ
RBM3D.Loop.GLoop:69 def RBM.Gauss.etaT : ℝ → ℝ → ℝ
RBM3D.Loop.GLoop:85 def RBM.Gauss.Gsig : (d L W : ℕ) → [NeZero L] → RBM.Gauss.Omega d L W → ℝ → ℝ → Bool → Matrix (RBM.Gauss.Vtx d L W) (RBM.Gauss.Vtx d L W) ℂ
RBM3D.Loop.GLoop:91 def RBM.Gauss.gloop : (d L W : ℕ) → [NeZero L] → RBM.Gauss.Omega d L W → ℝ → ℝ → {n : ℕ} → (Fin n → Bool) → (Fin n → RBM.Zd d L) → ℂ
RBM3D.Loop.GLoop:96 def RBM.Gauss.loopMax : (d L W : ℕ) → [NeZero L] → RBM.Gauss.Omega d L W → ℝ → ℝ → ℕ → ℝ
```

### A.2 RBM2D `c9a24cf`: the vocabulary files (script `inv.py --sig 150`, output verbatim; first line of each block = `file<TAB>lines<TAB>#public defs<TAB>#public theorems`)

```
RBM2D/Gauss/Model.lean	574	26	50
  L39 abbrev RBM.Gauss.Idx 
  L42 def RBM.Gauss.svar (i j : Idx L W) : ℝ
  L88 def RBM.Gauss.idxKey (i : Idx L W) : ℕ
  L102 abbrev RBM.Gauss.Coord 
  L105 abbrev RBM.Gauss.Ω 
  L108 def RBM.Gauss.gvar (c : Coord L W) : ℝ≥0
  L127 def RBM.Gauss.P : Measure (Ω L W)
  L130 instance RBM.Gauss.isProbabilityMeasure_P isProbabilityMeasure_P : IsProbabilityMeasure (P L W)
  L147 def RBM.Gauss.Xentry (ω : Ω L W) (i j : Idx L W) : ℂ
  L155 def RBM.Gauss.Xmat (ω : Ω L W) : Matrix (Idx L W) (Idx L W) ℂ
  L270 def RBM.Gauss.Xlinear : Ω L W →ₗ[ℝ] Matrix (Idx L W) (Idx L W) ℂ
  L277 def RBM.Gauss.coordinateMatrix (c : Coord L W) : Matrix (Idx L W) (Idx L W) ℂ
  L327 def RBM.Gauss.Hflow (u : ℝ) (ω : Ω L W) : Matrix (Idx L W) (Idx L W) ℂ
  L405 structure RBM.Gauss.Sizes 
  L415 instance RBM.Gauss.Sizes.neZeroL neZeroL (n : ℕ) : NeZero (d.L n)
  L416 instance RBM.Gauss.Sizes.neZeroW neZeroW (n : ℕ) : NeZero (d.W n)
  L419 def RBM.Gauss.Sizes.size (n : ℕ) : ℕ
  L425 abbrev RBM.Gauss.Sizes.SeqCoord 
  L428 abbrev RBM.Gauss.Sizes.SeqΩ 
  L430 def RBM.Gauss.Sizes.seqGvar (c : SeqCoord d) : ℝ≥0
  L434 def RBM.Gauss.Sizes.seqP : Measure (SeqΩ d)
  L437 instance RBM.Gauss.Sizes.isProbabilityMeasure_seqP isProbabilityMeasure_seqP : IsProbabilityMeasure (seqP d)
  L442 def RBM.Gauss.Sizes.slice (n : ℕ) (ω : SeqΩ d) : Ω (d.L n) (d.W n)
  L490 def RBM.Gauss.Sizes.seqXmat (n : ℕ) (ω : SeqΩ d) : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ
  L495 def RBM.Gauss.Sizes.seqHflow (n : ℕ) (u : ℝ) (ω : SeqΩ d) : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ
  L566 def RBM.Gauss.Sizes.constantSizes : Sizes
RBM2D/Defs/StochDom.lean	611	8	27
  L87 def RBM.badSet (ξ ζ : ∀ N, U N → Ω → ℝ) (τ : ℝ) (N : ℕ) : Set Ω
  L91 def RBM.StochDom (ξ ζ : ∀ N, U N → Ω → ℝ) : Prop
  L98 def RBM.badSetAt (size : ℕ → ℕ) (ξ ζ : ∀ l, U l → Ω → ℝ) (τ : ℝ) (l : ℕ) : Set Ω
  L103 def RBM.StochDomAt (size : ℕ → ℕ) (ξ ζ : ∀ l, U l → Ω → ℝ) : Prop
  L108 def RBM.NormStochDom {E : Type*} [Norm E] (A : ∀ N, U N → Ω → E) (ζ : ∀ N, U N → Ω → ℝ) : Prop
  L113 def RBM.DepNormStochDom {E : ℕ → Type*} [∀ N, Norm (E N)] (A : ∀ N, U N → Ω → E N) (ζ : ∀ N, U N → Ω → ℝ) : Prop
  L118 def RBM.HighProb (Ξ : ℕ → Set Ω) : Prop
  L122 def RBM.HighProbIn (Ξ Ω' : ℕ → Set Ω) : Prop
RBM2D/Defs/Semicircle.lean	346	8	6
  L28 def RBM.mscDisc (z : ℂ) : ℂ
  L36 def RBM.mscRoot₁ (z : ℂ) : ℂ
  L38 def RBM.mscRoot₂ (z : ℂ) : ℂ
  L42 def RBM.msc (z : ℂ) : ℂ
  L101 def RBM.lemE (z : ℂ) : ℝ
  L104 def RBM.lemT (z : ℂ) : ℝ
  L294 def RBM.ellz (L : ℕ) (z : ℂ) : ℝ
  L298 def RBM.Meta (L W : ℕ) (z : ℂ) : ℝ
RBM2D/Defs/SemicircleIntegral.lean	255	0	1
RBM2D/Path/Scales.lean	344	5	12
  L38 def RBM.Path.etaT (E u : ℝ) : ℝ
  L41 def RBM.Path.ellT (L : ℕ) (u : ℝ) : ℝ
  L44 def RBM.Path.scaleM (L W : ℕ) (E u : ℝ) : ℝ
  L48 def RBM.Path.tailT (L W : ℕ) (E D u ℓ : ℝ) : ℝ
  L52 def RBM.Path.ellStar (L W : ℕ) (u : ℝ) : ℝ
RBM2D/Hierarchy/ContractionBasic.lean	72	0	3
RBM2D/Hierarchy/ContractionCutWords.lean	117	2	4
  L26 def RBM.cutLeftChain (σ₁ σ₃ : List Bool) (a₁ a₃ : List (Z2 L)) (s t : Bool) (c : Z2 L) : Matrix (BlockIndex L W) (BlockIndex L W) ℂ
  L34 def RBM.cutRightChain (σ₂ : List Bool) (a₂ : List (Z2 L)) (s t : Bool) (a : Z2 L) : Matrix (BlockIndex L W) (BlockIndex L W) ℂ
RBM2D/Hierarchy/ContractionDirections.lean	198	0	9
RBM2D/Hierarchy/ContractionDrift.lean	81	0	3
RBM2D/Hierarchy/ContractionEdgeSplits.lean	66	2	2
  L15 structure RBM.Gauss.EdgeSplit (α : Type*)
  L21 def RBM.Gauss.edgeSplits {α : Type*} : List α → List (EdgeSplit α) | [] => [] | x :: xs => ⟨[], x, xs⟩ :: (edgeSplits xs).map (fun e => ⟨x :: e.before, e.selected, e.after⟩) t
RBM2D/Hierarchy/ContractionFirstDerivativePositionSum.lean	77	2	1
  L19 def RBM.Gauss.coordinateWordProduct (u : ℝ) (ω : Ω L W) (z : ℂ) (l : List (Bool × Z2 L)) : Matrix (BlockIndex L W) (BlockIndex L W) ℂ
  L24 def RBM.Gauss.coordinateEdgeTerm (u : ℝ) (ω : Ω L W) (γ : Coord L W) (z : ℂ) (e : EdgeSplit (Bool × Z2 L)) : Matrix (BlockIndex L W) (BlockIndex L W) ℂ
RBM2D/Hierarchy/ContractionPairPositionCut.lean	80	0	2
RBM2D/Hierarchy/ContractionPairSplits.lean	107	2	3
  L15 structure RBM.Gauss.PairSplit (α : Type*)
  L23 def RBM.Gauss.pairSplits {α : Type*} (l : List α) : List (PairSplit α)
RBM2D/Hierarchy/ContractionPositionLoopBridge.lean	80	1	4
  L19 def RBM.Gauss.segmentLoopIdx (l : List (Bool × Z2 L)) : LoopIdx (Z2 L)
RBM2D/Hierarchy/ContractionSameEdgePositionCut.lean	69	0	2
RBM2D/Hierarchy/ContractionSecondDerivativePositionSum.lean	151	4	1
  L19 def RBM.Gauss.coordinateSameEdgeTerm (u : ℝ) (ω : Ω L W) (γ : Coord L W) (z : ℂ) (e : EdgeSplit (Bool × Z2 L)) : Matrix (BlockIndex L W) (BlockIndex L W) ℂ
  L27 def RBM.Gauss.coordinatePairTerm (u : ℝ) (ω : Ω L W) (γ : Coord L W) (z : ℂ) (p : PairSplit (Bool × Z2 L)) : Matrix (BlockIndex L W) (BlockIndex L W) ℂ
  L57 def RBM.Gauss.coordinateSameEdgeSum (u : ℝ) (ω : Ω L W) (γ : Coord L W) (z : ℂ) (l : List (Bool × Z2 L)) : Matrix (BlockIndex L W) (BlockIndex L W) ℂ
  L64 def RBM.Gauss.coordinatePairSum (u : ℝ) (ω : Ω L W) (γ : Coord L W) (z : ℂ) (l : List (Bool × Z2 L)) : Matrix (BlockIndex L W) (BlockIndex L W) ℂ
RBM2D/Hierarchy/ContractionSecondDerivativeTraceSum.lean	52	0	1
RBM2D/Hierarchy/ContractionSecondLoop.lean	201	0	4
RBM2D/Hierarchy/ContractionSecondLoopAllCuts.lean	111	2	3
  L20 def RBM.Gauss.sameEdgeCutValue (u : ℝ) (ω : Ω L W) (z : ℂ) (e : EdgeSplit (Bool × Z2 L)) : ℂ
  L33 def RBM.Gauss.pairCutValue (u : ℝ) (ω : Ω L W) (z : ℂ) (p : PairSplit (Bool × Z2 L)) : ℂ
RBM2D/Hierarchy/ContractionSecondLoopExpectedCuts.lean	358	2	9
  L134 def RBM.Gauss.sameEdgeCutIntegrand (u : ℝ) (ω : Ω L W) (z : ℂ) (e : EdgeSplit (Bool × Z2 L)) (p q : Z2 L) : ℂ
  L145 def RBM.Gauss.pairCutIntegrand (u : ℝ) (ω : Ω L W) (z : ℂ) (p : PairSplit (Bool × Z2 L)) (v w : Z2 L) : ℂ
RBM2D/Hierarchy/ContractionSecondLoopPositionSum.lean	48	0	1
RBM2D/Hierarchy/ContractionSecondLoopReverse.lean	42	0	1
RBM2D/Hierarchy/ContractionSecondLoopSameEdge.lean	129	0	3
RBM2D/Hierarchy/ContractionSecondLoopSameEdgeCut.lean	72	0	3
RBM2D/Hierarchy/ContractionSecondLoopSameEdgeWord.lean	86	0	2
RBM2D/Hierarchy/ContractionSum.lean	214	2	4
  L94 def RBM.Gauss.usedCoords : Finset (Coord L W)
  L156 def RBM.Gauss.blockRelabel (A : Matrix (Idx L W) (Idx L W) ℂ) : Matrix (BlockIndex L W) (BlockIndex L W) ℂ
RBM2D/Hierarchy/ContractionUnused.lean	120	0	5
RBM2D/Hierarchy/LoopHierarchyCutBlockSumBound.lean	118	1	3
  L25 def RBM.Gauss.cutResolventEnvelope (η : ℝ) (n : ℕ) : ℝ
RBM2D/Hierarchy/LoopHierarchyCutContinuity.lean	321	0	13
RBM2D/Hierarchy/LoopHierarchyCutLengths.lean	151	3	5
  L20 def RBM.Gauss.sameEdgeOuterIdx (e : EdgeSplit (Bool × Z2 L)) (p : Z2 L) : LoopIdx (Z2 L)
  L28 def RBM.Gauss.sameEdgeInnerIdx (e : EdgeSplit (Bool × Z2 L)) (q : Z2 L) : LoopIdx (Z2 L)
  L32 def RBM.Gauss.pairBaseIdx (p : PairSplit (Bool × Z2 L)) : LoopIdx (Z2 L)
RBM2D/Hierarchy/LoopHierarchyCutNormBounds.lean	169	0	5
RBM2D/Hierarchy/LoopHierarchyCutTotalBound.lean	131	0	5
RBM2D/Hierarchy/LoopHierarchyDerivativeBound.lean	87	0	3
RBM2D/Hierarchy/LoopHierarchyEnvelopeLabelSum.lean	165	1	4
  L58 def RBM.Gauss.loopHierarchyLengthEnvelope (η : ℝ) (E : ℝ) (n : ℕ) : ℝ
RBM2D/Hierarchy/LoopHierarchyFirstDuhamel.lean	59	0	2
RBM2D/Hierarchy/LoopHierarchyFromInitialBound.lean	89	0	3
RBM2D/Hierarchy/LoopHierarchyGenerator.lean	93	3	1
  L24 def RBM.Gauss.expectedSameEdgeCuts (E u : ℝ) (I : LoopIdx (Z2 L)) : ℂ
  L30 def RBM.Gauss.expectedPairCuts (E u : ℝ) (I : LoopIdx (Z2 L)) : ℂ
  L36 def RBM.Gauss.expectedSpectralCuts (E u : ℝ) (I : LoopIdx (Z2 L)) : ℂ
RBM2D/Hierarchy/LoopHierarchyInitialAverageBound.lean	90	0	2
RBM2D/Hierarchy/LoopHierarchyIntegral.lean	88	1	2
  L25 def RBM.Gauss.expectedLoopCutRHS (E u : ℝ) (I : LoopIdx (Z2 L)) : ℂ
RBM2D/Hierarchy/LoopHierarchyIntegralBound.lean	86	1	2
  L26 def RBM.Gauss.loopHierarchyUniformEnvelope (η : ℝ) (E : ℝ) (I : LoopIdx (Z2 L)) : ℝ
RBM2D/Hierarchy/LoopHierarchyIntegralZero.lean	87	0	3
RBM2D/Hierarchy/LoopHierarchyLengthEnvelopeMonotone.lean	91	0	6
RBM2D/Hierarchy/LoopHierarchyLengthEnvelopeSmall.lean	101	0	5
RBM2D/Hierarchy/LoopHierarchyOneEdge.lean	99	0	6
RBM2D/Hierarchy/LoopHierarchyRHSBound.lean	113	0	3
RBM2D/Hierarchy/LoopHierarchySpectralCutBounds.lean	159	0	5
RBM2D/Hierarchy/LoopHierarchyTwoEdge.lean	110	0	6
RBM2D/Hierarchy/Loops.lean	275	6	15
  L28 structure RBM.LoopIdx (α : Type*)
  L36 def RBM.LoopIdx.WF {α : Type*} (I : LoopIdx α) : Prop
  L39 def RBM.LoopIdx.length {α : Type*} (I : LoopIdx α) : ℕ
  L48 def RBM.Gsig (H : Matrix n n ℂ) (z : ℂ) (σ : Bool) : Matrix n n ℂ
  L86 def RBM.gloopProd (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ) (I : LoopIdx (Z2 L)) : Matrix (BlockIndex L W) (BlockIndex L W) ℂ
  L92 def RBM.gloop (H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) (z : ℂ) (I : LoopIdx (Z2 L)) : ℂ
RBM2D/Hierarchy/Operations.lean	99	1	6
  L27 def RBM.LoopIdx.cutGlue (k : ℕ) (b : α) (I : LoopIdx α) : LoopIdx α
RBM2D/Hierarchy/OperationsPair.lean	71	2	5
  L23 def RBM.LoopIdx.cutGlueL (k l : ℕ) (b : α) (I : LoopIdx α) : LoopIdx α
  L28 def RBM.LoopIdx.cutGlueR (k l : ℕ) (b : α) (I : LoopIdx α) : LoopIdx α
RBM2D/Hierarchy/OperationsPairWord.lean	142	0	6
RBM2D/Hierarchy/WardResolvent.lean	193	0	6
RBM2D/Induction/Defs.lean	453	36	0
  L62 def RBM.Ind.SizeTendsto : Prop
  L71 def RBM.Ind.lkGen (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Z2 L) : ℝ
  L76 def RBM.Ind.xiL (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (k : ℕ) : ℝ
  L83 def RBM.Ind.xiLK (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (k : ℕ) : ℝ
  L90 def RBM.Ind.Ugen (E : ℝ) {k : ℕ} [NeZero k] (σ : Fin k → Bool) (v w : ℝ) (A : (Fin k → Z2 L) → ℂ) (a : Fin k → Z2 L) : ℂ
  L96 def RBM.Ind.tmax {k : ℕ} (A : (Fin k → Z2 L) → ℂ) : ℝ
  L101 def RBM.Ind.HasDecay (u τ D : ℝ) {k : ℕ} (A : (Fin k → Z2 L) → ℂ) : Prop
  L106 def RBM.Ind.SumZero {k : ℕ} [NeZero k] (A : (Fin k → Z2 L) → ℂ) : Prop
  L111 def RBM.Ind.Symmetric {k : ℕ} [NeZero k] (A : (Fin k → Z2 L) → ℂ) : Prop
  L116 def RBM.Ind.UgenPair (E : ℝ) {k : ℕ} [NeZero k] (σ : Fin k → Bool) (v w : ℝ) (A : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ) (a : Fin k → Z2 L) : ℂ
  L125 def RBM.Ind.tmax2 {k : ℕ} (A : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ) : ℝ
  L129 def RBM.Ind.HasDecay2 (u τ D : ℝ) {k : ℕ} (A : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ) : Prop
  L134 def RBM.Ind.DoubleSumZero {k : ℕ} [NeZero k] (A : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ) : Prop
  L141 def RBM.Ind.gEntry (E s : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (σ : Bool) (x y : Idx L W) : ℂ
  L151 structure RBM.Ind.LocalForm (L W k K : ℕ)
  L159 def RBM.Ind.LocalForm.eval (F : LocalForm L W k K) (E s : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (b : Fin k → Z2 L) : ℂ
  L166 def RBM.Ind.LocalForm.Local (F : LocalForm L W k K) (τ s : ℝ) : Prop
  L179 def RBM.Ind.KboundConcl (κ : ℝ) : Prop
  L188 def RBM.Ind.Step2TargetN (κ c τ : ℝ) (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop
  L199 def RBM.Ind.InitLK (E : ℕ → ℝ) (s : ℕ → ℝ) : Prop
  L206 def RBM.Ind.gMax {L W : ℕ} [NeZero L] [NeZero W] (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) : ℝ
  L212 def RBM.Ind.Step1LoopUnif (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop
  L220 def RBM.Ind.Step1WeakLawUnif (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop
  L229 def RBM.Ind.MainIndHyp (κ c τ : ℝ) (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop
  L237 abbrev RBM.Ind.PT (s t : ℕ → ℝ) (ξ ζ : ∀ n, Path.TimeIcc s t n → Sizes.SeqΩ d → ℝ) : Prop
  L247 def RBM.Ind.STOeqPT (E : ℕ → ℝ) (s t : ℕ → ℝ) (k : ℕ) : Prop
  L268 def RBM.Ind.PPTwoLoopPT (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop
  L277 def RBM.Ind.Step3PT (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop
  L284 def RBM.Ind.Step4PT (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop
  L292 def RBM.Ind.Step5PT (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop
  L302 def RBM.Ind.MainIndConcl (E : ℕ → ℝ) (t : ℕ → ℝ) : Prop
  L308 def RBM.Ind.MLConcl (E : ℕ → ℝ) (t : ℕ → ℝ) : Prop
  L318 def RBM.Ind.chainTime (t : ℕ → ℝ) (n₀ k : ℕ) (n : ℕ) : ℝ
  L325 def RBM.Ind.MLRegion (κ τ : ℝ) (n : ℕ) : Type
  L329 def RBM.Ind.GtLocalRegionPT (κ τ : ℝ) : Prop
  L338 def RBM.Ind.GtLocalRegionUnif (κ τ : ℝ) : Prop
RBM2D/Induction/HierVocab.lean	664	47	0
  L62 def RBM.Ind.Psum {k : ℕ} [NeZero k] (A : (Fin k → Z2 L) → ℂ) (a₁ : Z2 L) : ℂ
  L66 def RBM.Ind.vartheta {k : ℕ} [NeZero k] (t : ℝ) (a : Fin k → Z2 L) : ℂ
  L71 def RBM.Ind.varthetaDot {k : ℕ} [NeZero k] (t : ℝ) (a : Fin k → Z2 L) : ℂ
  L75 def RBM.Ind.Qop {k : ℕ} [NeZero k] (t : ℝ) (A : (Fin k → Z2 L) → ℂ) (a : Fin k → Z2 L) : ℂ
  L81 def RBM.Ind.thetaSig (E : ℝ) {k : ℕ} [NeZero k] (σ : Fin k → Bool) (u : ℝ) (A : (Fin k → Z2 L) → ℂ) (a : Fin k → Z2 L) : ℂ
  L95 def RBM.Ind.QopAlgebra : Prop
  L117 def RBM.Ind.QopNorm : Prop
  L126 def RBM.Ind.QopDecay : Prop
  L135 def RBM.Ind.QopDecayLiteral : Prop
  L141 def RBM.Ind.QopDecayLiteralRefuted : Prop
  L150 def RBM.Ind.LLf (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (I : LoopIdx (Z2 L)) : ℂ
  L154 def RBM.Ind.LKf (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (I : LoopIdx (Z2 L)) : ℂ
  L159 def RBM.Ind.ksimLK (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (l : ℕ) (I : LoopIdx (Z2 L)) : ℂ
  L170 def RBM.Ind.elklkN (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (I : LoopIdx (Z2 L)) : ℂ
  L176 def RBM.Ind.egtN (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (I : LoopIdx (Z2 L)) : ℂ
  L183 def RBM.Ind.eeLoop (σ : List Bool) (a a' : List (Z2 L)) (k : ℕ) (b b' : Z2 L) : LoopIdx (Z2 L)
  L190 def RBM.Ind.eeN (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) {n : ℕ} (σ : Fin n → Bool) (a a' : Fin n → Z2 L) : ℂ
  L196 def RBM.Ind.lkTensor (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) {k : ℕ} (σ : Fin k → Bool) : (Fin k → Z2 L) → ℂ
  L206 def RBM.Ind.HierarchyN : Prop
  L224 def RBM.Ind.KcalDecay (κ : ℝ) : Prop
  L236 def RBM.Ind.DecayLoopAt (κ c τ C₀ : ℝ) (E u P : ℕ → ℝ) : Prop
  L259 def RBM.Ind.DecayLoopWindow (κ c τ : ℝ) (E s t : ℕ → ℝ) : Prop
  L265 def RBM.Ind.DecayLoopFromML (κ c τ : ℝ) (E t : ℕ → ℝ) : Prop
  L273 abbrev RBM.Ind.IdxT (s t : ℕ → ℝ) (k : ℕ) (n : ℕ) : Type
  L277 def RBM.Ind.farInd (n : ℕ) (u τ' : ℝ) {k : ℕ} (a : Fin k → Z2 (d.L n)) : ℝ
  L284 def RBM.Ind.BcalEPT (κ c τ : ℝ) (E s t : ℕ → ℝ) : Prop
  L343 def RBM.Ind.B5 (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) {k : ℕ} [NeZero k] (σ : Fin k → Bool) (a : Fin k → Z2 L) : ℂ
  L348 def RBM.Ind.B4 (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) {k : ℕ} [NeZero k] (σ : Fin k → Bool) (a : Fin k → Z2 L) : ℂ
  L356 def RBM.Ind.Alternating {k : ℕ} [NeZero k] (σ : Fin k → Bool) : Prop
  L365 def RBM.Ind.B45PT (κ c τ : ℝ) (E s t Λ : ℕ → ℝ) (k : ℕ) [NeZero k] : Prop
  L387 def RBM.Ind.AvecN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool) (ω : PathΩ d) : (Fin k → Z2 (d.L n)) → ℂ
  L394 def RBM.Ind.martIncN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool) (ω : PathΩ d) : (Fin k → Z2 (d.L n)) → ℂ
  L400 def RBM.Ind.predIncN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} [NeZero k] (σ : Fin k → Bool) (ω : PathΩ d) : (Fin k → Z2 (d.L n)) → ℂ
  L409 def RBM.Ind.StoppedDuhamelN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) : Prop
  L421 def RBM.Ind.kStepC (L W k : ℕ) (Bk : ℝ) : ℝ
  L427 def RBM.Ind.uStepC (k : ℕ) (Δ v : ℝ) : ℝ
  L432 def RBM.Ind.stepErrN (L W : ℕ) (E : ℝ) (k : ℕ) (u v Δ Bk : ℝ) : ℝ
  L440 def RBM.Ind.GridDriftN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) : Prop
  L456 def RBM.Ind.StoppedAzumaN [IsFiniteMeasure (pathP d)] (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) : Prop
  L479 def RBM.Ind.loopDerivN (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ) (M X : Matrix (Idx L W) (Idx L W) ℂ) {k : ℕ} (σ : Fin k → Bool) (b : Fin k → Z2 L) : ℂ
  L486 def RBM.Ind.QVPropagatedN : Prop
  L504 def RBM.Ind.STOeqTargetV2 (κ c τ : ℝ) (C : ℕ → ℝ) (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop
  L511 def RBM.Ind.PPTargetV2 (κ c τ : ℝ) (C : ℕ → ℝ) (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop
  L518 def RBM.Ind.MainIndPinV2 (κ c τ : ℝ) (C : ℕ → ℝ) : Prop
  L525 def RBM.Ind.MLExpPin (κ c τ : ℝ) (C : ℕ → ℝ) (E t : ℕ → ℝ) : Prop
  L539 def RBM.Ind.llPairN (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) (I : LoopIdx (Z2 L)) : ℂ
  L548 def RBM.Ind.LoopGenN : Prop
RBM2D/Evolution/Defs.lean	219	13	0
  L33 def RBM.Evol.ratioR (E s t : ℝ) : ℝ
  L37 def RBM.Evol.rhoR (s t : ℝ) : ℝ
  L42 def RBM.Evol.DecayWin {k : ℕ} (ρ δA : ℝ) (A : (Fin k → Z2 L) → ℂ) : Prop
  L46 def RBM.Evol.DecayWin2 {k : ℕ} (ρ δA : ℝ) (A : (Fin k → Z2 L) → (Fin k → Z2 L) → ℂ) : Prop
  L55 def RBM.Evol.cPrec (𝔠 : ℝ) (k : ℕ) : ℝ
  L64 def RBM.Evol.SumDecayDetPrec (κ 𝔠 δ : ℝ) (C : ℕ → ℝ) : Prop
  L85 def RBM.Evol.SumDecayCase5Prec (κ 𝔠 δ : ℝ) (C : ℕ → ℝ) : Prop
  L99 def RBM.Evol.LabelDecayPT {k K : ℕ} (E u : ℕ → ℝ) (F : ∀ n, LocalForm (d.L n) (d.W n) k K) (τ D : ℝ) : Prop
  L109 def RBM.Evol.oneLoopExpErr (n : ℕ) (E u : ℝ) (a : Z2 (d.L n)) : ℂ
  L115 def RBM.Evol.expLoopErr (n : ℕ) (E t : ℝ) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Z2 (d.L n)) : ℂ
  L120 def RBM.Evol.Step61Concl (E u : ℕ → ℝ) : Prop
  L127 def RBM.Evol.DecayLoopPT (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop
  L138 def RBM.Evol.MLExpConcl (E t : ℕ → ℝ) : Prop
RBM2D/Endpoints.lean	268	20	2
  L51 def RBM.Endpoints.mSC (z : ℂ) : ℂ
  L56 def RBM.Endpoints.IsOrthoEigenbasis {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (μ : ι → ℝ) (ψ : ι → ι → ℂ) : Prop
  L63 def RBM.Endpoints.Admissible (𝔠 : ℝ) (d : Sizes) : Prop
  L68 def RBM.Endpoints.Gn (d : Sizes) (n : ℕ) (ω : SeqΩ d) (z : ℂ) : Matrix (Idx (d.L n) (d.W n)) (Idx (d.L n) (d.W n)) ℂ
  L74 def RBM.Endpoints.locDomain (N : ℕ) (κ τ : ℝ) (z : ℂ) : Prop
  L81 def RBM.Endpoints.decolEvent (d : Sizes) (n : ℕ) (κ τ : ℝ) (ω : SeqΩ d) : Prop
  L88 def RBM.Endpoints.decol : Prop
  L99 def RBM.Endpoints.locSC : Prop
  L118 def RBM.Endpoints.window {ι : Type*} (N W : ℕ) (τ E : ℝ) (μ : ι → ℝ) (k : ι) : Prop
  L123 def RBM.Endpoints.queBad (d : Sizes) (n : ℕ) (τ E : ℝ) (a : Z2 (d.L n)) (ω : SeqΩ d) : Prop
  L134 def RBM.Endpoints.que2Bad (d : Sizes) (n : ℕ) (τ E : ℝ) (A : Finset (Z2 (d.L n))) (ω : SeqΩ d) : Prop
  L145 def RBM.Endpoints.QUE : Prop
  L159 def RBM.Endpoints.trGEGE (d : Sizes) (n : ℕ) (ω : SeqΩ d) (z : ℂ) (σ : Bool) (a b : Z2 (d.L n)) : ℂ
  L166 def RBM.Endpoints.profile (L W : ℕ) [NeZero L] (z : ℂ) (σ : Bool) (a b : Z2 L) : ℂ
  L173 def RBM.Endpoints.QDiff : Prop
  L190 def RBM.Endpoints.gueVar (L W : ℕ) (c : Coord L W) : NNReal
  L196 def RBM.Endpoints.gueP (L W : ℕ) : Measure (Ω L W)
  L202 def RBM.Endpoints.kPoint {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) (O : (Fin k → ℝ) → ℝ) (E : ℝ) (lam : ι → ℝ) : ℝ
  L209 def RBM.Endpoints.BUniv : Prop
  L225 def RBM.Endpoints.witnessSizes : Sizes
```

## B. Classes and rules

* (a) dimension-free: copy with the renaming rules R1-R4 of the prove report (no exponent token in the file; every port still re-checks each statement against this paper, CLAUDE.md §5.2);
* (b) generalize `Z2 L -> Zd d L`, `W^2 -> W^d`, `(W L)^2 -> (W L)^d`, `S^(B)` with `g = lam n`, redo the exponents (file has an exponent token, or uses the d=2 scales `scaleM`, `ellT`, `tailT`, `Meta`, `ellz`);
* (c) d=2-specific argument, replaced by the d>=3 argument named in the labels column (hand list: Step 2, Step 6, the d=2 scales, `Kstab2`); the ST design ticket of that step confirms the list;
* (d) not needed: not in the import closure of the five endpoint theorems, deleted by RBM2D T2274 as dead code, or already in merged RBM3D (target column names the merged file).

Token rule (script `stats.py`): exponent tokens are `W ^ 2`, `L ^ 2`, `(W * L) ^ 2`, `size ^ 2`, `W⁻²`, `L²`, `d = 2`, `Z_L^2`, `5⁻¹`; the (a)/(b) split is by this rule only, so a (b) row may need less work and an (a) row more.
Labels are the labels cited in the file that also exist in the TeX of this paper (`labels.py`: `label@file:line`); (c) rows carry the replacement labels.

## C. One row per RBM2D file (nine directories)

### Defs -> RBM3D/Defs

| RBM2D file | lines c9a24cf | kept 0c1330a | class | RBM3D target | basis | labels (this paper) |
|---|---|---|---|---|---|---|
| Block.lean | 183 | 183 | d | RBM3D/Defs/Block.lean (SB, sbKernel, sbKernelR) | superseded by merged RBM3D | lem_propTH@1_2:1119 |
| Dist.lean | 140 | 125 | d | RBM3D/Defs/Lattice.lean (zdist, zdistD); `zdistInf` pinned in the probe | superseded by merged RBM3D | lem_propTH@1_2:1119 |
| Domination.lean | 208 | 150 | d | RBM3D/Defs/Domination.lean (UnifDetDom, DetDom) | superseded by merged RBM3D | lem_propTH@1_2:1119; stoch_domination@1_2:229 |
| Model.lean | 285 | 250 | b | RBM3D/Defs/Model.lean | exponent tokens 16 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| Semicircle.lean | 346 | 303 | d | RBM3D/Defs/Semicircle.lean (msc, lemE, lemT, mE, zt); `ellz`, `Meta` (d=2) replaced by merged Defs/Params.lean (ellT, Bparam) | superseded by merged RBM3D | zztE@1_2:787; eq:zztE@1_2:791 |
| SemicircleIntegral.lean | 255 | 219 | d | RBM3D/Defs/SemicircleIntegral.lean (ported by T2005, merged on main after the branch point of this ticket: theorem msc_eq_integral) | superseded by merged RBM3D |  |
| StochDom.lean | 611 | 131 | a | RBM3D/Defs/StochDom.lean | merged Defs/StochDom.lean covers the index-scale part; port StochDomAt/NormStochDom variants/Absorb section |  |

### Evolution -> RBM3D/Evolution

| RBM2D file | lines c9a24cf | kept 0c1330a | class | RBM3D target | basis | labels (this paper) |
|---|---|---|---|---|---|---|
| Bridge.lean | 461 | 425 | b | RBM3D/Evolution/Bridge.lean | exponent tokens 11 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | sum_res_1@3_5:1639 |
| Case3.lean | 4275 | 3828 | b | RBM3D/Evolution/Case3.lean | exponent tokens 68 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | lem:sum_decay@3_5:1632; lem:main_ind@1_2:1256 |
| Case3Defs.lean | 182 | 147 | b | RBM3D/Evolution/Case3Defs.lean | no exponent token but 4 uses of the d=2 scales (scaleM, ellT, tailT, Meta, ellz): replace by ell_t (eq:ellt), B_{t,K} (eq_B_param), W^{-d}B_{t,0} | lem_GbEXP@3_5:14; GijGEX@3_5:24 |
| Case4.lean | 1891 | 1732 | b | RBM3D/Evolution/Case4.lean | exponent tokens 72 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | lem:sum_decay@3_5:1632; sumAzero@3_5:1655 |
| Case5.lean | 1562 | 1439 | b | RBM3D/Evolution/Case5.lean | exponent tokens 63 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | lem:sum_decay@3_5:1632 |
| CltDecorrelation.lean | 403 | 392 | b | RBM3D/Evolution/CltDecorrelation.lean | exponent tokens 4 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| CltGood.lean | 697 | 615 | b | RBM3D/Evolution/CltGood.lean | exponent tokens 14 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Eq:Gdecay_w@1_2:1349; GijGEX@3_5:24; Gt_bound_flow@1_2:1342 |
| CltMoments.lean | 2281 | 2094 | b | RBM3D/Evolution/CltMoments.lean | exponent tokens 3 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| CltPath.lean | 320 | 283 | b | RBM3D/Evolution/CltPath.lean | no exponent token but 11 uses of the d=2 scales (scaleM, ellT, tailT, Meta, ellz): replace by ell_t (eq:ellt), B_{t,K} (eq_B_param), W^{-d}B_{t,0} |  |
| CltResolvent.lean | 977 | 728 | b | RBM3D/Evolution/CltResolvent.lean | exponent tokens 16 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| CltStep.lean | 737 | 730 | b | RBM3D/Evolution/CltStep.lean | exponent tokens 1 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| CltSwap.lean | 385 | 329 | b | RBM3D/Evolution/CltSwap.lean | exponent tokens 3 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| Defs.lean | 219 | 145 | b | RBM3D/Evolution/Defs.lean | exponent tokens 6 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | lem_GbEXP@3_5:14; Main_DEL_COND@1_2:359; deccA0@3_5:1634; lem_decayLoop@3_5:1126; res_decayLK@3_5:1128; sum_res_1@3_5:1639 |
| FarEntry.lean | 895 | 817 | b | RBM3D/Evolution/FarEntry.lean | exponent tokens 19 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Eq:Gdecay_w@1_2:1349; GijGEX@3_5:24; lem_GbEXP@3_5:14 |
| KernelExpand.lean | 612 | 581 | b | RBM3D/Evolution/KernelExpand.lean | exponent tokens 19 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | lem:sum_decay@3_5:1632; sum_res_1@3_5:1639 |
| LatticeSums.lean | 92 | 82 | b | RBM3D/Evolution/LatticeSums.lean | mixed lattice sum over Z_L^2 (eq-1sum, 7:206): d enters through the shell count; redo with merged Defs/Shells.lean, RadialSum.lean |  |
| MLExpDrift.lean | 1673 | 1614 | c | RBM3D/Evolution/MLExpDrift.lean (re-written) | Step 6 (ML:exp) of d>=3 rests on the diagrammatic light-weight estimate (sec. 7, lem:LWterm_EXP), which no sister project has (DECISIONS §2 item 3) | lem:improve_exp_aver@6:12, lem:LWterm_EXP@6:83, eq:ExpLWn=2@6:85, int_K-L+QE@6:109 |
| MLExpDuhamel.lean | 532 | 461 | c | RBM3D/Evolution/MLExpDuhamel.lean (re-written) | Step 6 (ML:exp) of d>=3 rests on the diagrammatic light-weight estimate (sec. 7, lem:LWterm_EXP), which no sister project has (DECISIONS §2 item 3) | lem:improve_exp_aver@6:12, lem:LWterm_EXP@6:83, eq:ExpLWn=2@6:85, int_K-L+QE@6:109; Eexpint_K-L@6:4 |
| MLExpHier.lean | 731 | 673 | c | RBM3D/Evolution/MLExpHier.lean (re-written) | Step 6 (ML:exp) of d>=3 rests on the diagrammatic light-weight estimate (sec. 7, lem:LWterm_EXP), which no sister project has (DECISIONS §2 item 3) | lem:improve_exp_aver@6:12, lem:LWterm_EXP@6:83, eq:ExpLWn=2@6:85, int_K-L+QE@6:109; pro_dyncalK@1_2:990 |
| MLExpInv.lean | 878 | 818 | c | RBM3D/Evolution/MLExpInv.lean (re-written) | Step 6 (ML:exp) of d>=3 rests on the diagrammatic light-weight estimate (sec. 7, lem:LWterm_EXP), which no sister project has (DECISIONS §2 item 3) | lem:improve_exp_aver@6:12, lem:LWterm_EXP@6:83, eq:ExpLWn=2@6:85, int_K-L+QE@6:109; Kn2sol@1_2:1175; lem_propTH@1_2:1119 |
| MLExpQ.lean | 1669 | 1558 | c | RBM3D/Evolution/MLExpQ.lean (re-written) | Step 6 (ML:exp) of d>=3 rests on the diagrammatic light-weight estimate (sec. 7, lem:LWterm_EXP), which no sister project has (DECISIONS §2 item 3) | lem:improve_exp_aver@6:12, lem:LWterm_EXP@6:83, eq:ExpLWn=2@6:85, int_K-L+QE@6:109; jywiiwsoks@3_5:1271; lem_+Q@3_5:1285 |
| MLExpVocab.lean | 1349 | 774 | c | RBM3D/Evolution/MLExpVocab.lean (re-written) | Step 6 (ML:exp) of d>=3 rests on the diagrammatic light-weight estimate (sec. 7, lem:LWterm_EXP), which no sister project has (DECISIONS §2 item 3) | lem:improve_exp_aver@6:12, lem:LWterm_EXP@6:83, eq:ExpLWn=2@6:85, int_K-L+QE@6:109; Def_Ktza@1_2:986; Eexpint_K-L@6:4; def_ELKLK@3_5:97; def_EwtG@1_2:961; eq_L-Keee@3_5:73; jywiiwsoks@3_5:1271; lem_+Q@3_5:1285 |
| Step61.lean | 1021 | 948 | c | RBM3D/Evolution/Step61.lean (re-written) | Step 6 (ML:exp) of d>=3 rests on the diagrammatic light-weight estimate (sec. 7, lem:LWterm_EXP), which no sister project has (DECISIONS §2 item 3) | lem:improve_exp_aver@6:12, lem:LWterm_EXP@6:83, eq:ExpLWn=2@6:85, int_K-L+QE@6:109; Eq:L-KGt@1_2:1195 |
| XiBounds.lean | 783 | 734 | b | RBM3D/Evolution/XiBounds.lean | exponent tokens 32 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | lem:sum_decay@3_5:1632 |

### Gauss -> RBM3D/Gauss

| RBM2D file | lines c9a24cf | kept 0c1330a | class | RBM3D target | basis | labels (this paper) |
|---|---|---|---|---|---|---|
| Domination.lean | 661 | 276 | a | RBM3D/Gauss/Domination.lean | moment => domination bridge, generic; merged Gauss/Domination.lean has the index-scale part; port the *At variants |  |
| Envelope.lean | 308 | 175 | a | RBM3D/Gauss/Envelope.lean | deterministic envelope, generic; merged Gauss/Envelope.lean has the index-scale part |  |
| FlowDerivative.lean | 48 | -1 | d | none | deleted by RBM2D T2274 (dead code of the final d=2 proof, commit 99d6fe0) |  |
| FlowTimeCont.lean | 61 | 28 | a | RBM3D/Gauss/FlowTimeCont.lean | no exponent token; renaming R1-R4 only (lattice tokens 4, Sizes tokens 9) |  |
| GreenCoordinateSecondDerivative.lean | 90 | 58 | a | RBM3D/Gauss/GreenCoordinateSecondDerivative.lean | no exponent token; renaming R1-R4 only (lattice tokens 8, Sizes tokens 0) |  |
| GreenDerivative.lean | 143 | 99 | a | RBM3D/Gauss/GreenDerivative.lean | no exponent token; renaming R1-R4 only (lattice tokens 18, Sizes tokens 0) |  |
| GreenTimeCont.lean | 94 | 81 | a | RBM3D/Gauss/GreenTimeCont.lean | no exponent token; renaming R1-R4 only (lattice tokens 1, Sizes tokens 0) |  |
| LinearForm.lean | 282 | 204 | a | RBM3D/Gauss/LinearForm.lean | linear forms in the Gaussian coordinates of seqP |  |
| LoopCoordinateDerivative.lean | 234 | 163 | a | RBM3D/Gauss/LoopCoordinateDerivative.lean | no exponent token; renaming R1-R4 only (lattice tokens 51, Sizes tokens 0) |  |
| LoopCoordinateDerivativeBounds.lean | 252 | 252 | b | RBM3D/Gauss/LoopCoordinateDerivativeBounds.lean | exponent tokens 10 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| LoopCoordinateIntegrability.lean | 158 | 113 | b | RBM3D/Gauss/LoopCoordinateIntegrability.lean | exponent tokens 2 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| LoopCoordinateSecondDerivative.lean | 176 | 134 | a | RBM3D/Gauss/LoopCoordinateSecondDerivative.lean | no exponent token; renaming R1-R4 only (lattice tokens 29, Sizes tokens 0) |  |
| LoopCoordinateStein.lean | 58 | -1 | d | none | deleted by RBM2D T2274 (dead code of the final d=2 proof, commit 99d6fe0) |  |
| LoopCoordinateSteinSum.lean | 90 | -1 | d | none | deleted by RBM2D T2274 (dead code of the final d=2 proof, commit 99d6fe0) |  |
| LoopDerivative.lean | 203 | 128 | a | RBM3D/Gauss/LoopDerivative.lean | no exponent token; renaming R1-R4 only (lattice tokens 40, Sizes tokens 0) |  |
| LoopEnvelope.lean | 131 | 119 | b | RBM3D/Gauss/LoopEnvelope.lean | exponent tokens 17 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| LoopEnvelopeSharp.lean | 116 | -1 | d | none | unreachable from Main/Endpoints.lean + Main/BUnivHolds.lean (import closure) |  |
| LoopExpectationDerivative.lean | 102 | 102 | b | RBM3D/Gauss/LoopExpectationDerivative.lean | exponent tokens 2 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| LoopFlowCoordinateChain.lean | 216 | 181 | a | RBM3D/Gauss/LoopFlowCoordinateChain.lean | no exponent token; renaming R1-R4 only (lattice tokens 32, Sizes tokens 0) |  |
| LoopFlowDerivativeEnvelope.lean | 200 | 195 | b | RBM3D/Gauss/LoopFlowDerivativeEnvelope.lean | exponent tokens 15 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| LoopFlowSteinExpectation.lean | 351 | 341 | b | RBM3D/Gauss/LoopFlowSteinExpectation.lean | exponent tokens 9 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| LoopGeneratorExpectation.lean | 106 | 106 | a | RBM3D/Gauss/LoopGeneratorExpectation.lean | no exponent token; renaming R1-R4 only (lattice tokens 2, Sizes tokens 0) |  |
| LoopGeneratorSamplewise.lean | 58 | 58 | b | RBM3D/Gauss/LoopGeneratorSamplewise.lean | exponent tokens 2 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| LoopInitialValue.lean | 54 | 35 | b | RBM3D/Gauss/LoopInitialValue.lean | exponent tokens 1 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| LoopInitialValueBound.lean | 126 | -1 | d | none | unreachable from Main/Endpoints.lean + Main/BUnivHolds.lean (import closure) |  |
| LoopInitialValueConstantCount.lean | 46 | -1 | d | none | unreachable from Main/Endpoints.lean + Main/BUnivHolds.lean (import closure) |  |
| LoopInitialValueEmpty.lean | 58 | -1 | d | none | deleted by RBM2D T2274 (dead code of the final d=2 proof, commit 99d6fe0) |  |
| LoopInitialValueGeneralLabelSum.lean | 109 | -1 | d | none | unreachable from Main/Endpoints.lean + Main/BUnivHolds.lean (import closure) |  |
| LoopInitialValueLabelSum.lean | 50 | -1 | d | none | unreachable from Main/Endpoints.lean + Main/BUnivHolds.lean (import closure) |  |
| LoopInitialValueProjectionWords.lean | 113 | 105 | b | RBM3D/Gauss/LoopInitialValueProjectionWords.lean | exponent tokens 5 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| LoopInitialValueScalar.lean | 119 | 98 | b | RBM3D/Gauss/LoopInitialValueScalar.lean | exponent tokens 3 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| LoopInitialValueSupport.lean | 88 | 60 | b | RBM3D/Gauss/LoopInitialValueSupport.lean | exponent tokens 4 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| LoopInitialValueThreeLabelSum.lean | 65 | -1 | d | none | unreachable from Main/Endpoints.lean + Main/BUnivHolds.lean (import closure) |  |
| LoopMomentCont.lean | 85 | -1 | d | none | deleted by RBM2D T2274 (dead code of the final d=2 proof, commit 99d6fe0) |  |
| LoopSampleCont.lean | 85 | 76 | a | RBM3D/Gauss/LoopSampleCont.lean | no exponent token; renaming R1-R4 only (lattice tokens 10, Sizes tokens 0) |  |
| LoopSpectralDriftCuts.lean | 210 | 203 | b | RBM3D/Gauss/LoopSpectralDriftCuts.lean | exponent tokens 3 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| LoopSpectralDriftExpectation.lean | 136 | -1 | d | none | deleted by RBM2D T2274 (dead code of the final d=2 proof, commit 99d6fe0) |  |
| LoopTimeCont.lean | 106 | 87 | a | RBM3D/Gauss/LoopTimeCont.lean | no exponent token; renaming R1-R4 only (lattice tokens 14, Sizes tokens 0) |  |
| Model.lean | 574 | 456 | b | RBM3D/Gauss/Model.lean | exponent tokens 3 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| MomentBridge.lean | 369 | 160 | a | RBM3D/Gauss/MomentBridge.lean | no exponent token; renaming R1-R4 only (lattice tokens 2, Sizes tokens 0) |  |
| MomentTimeCont.lean | 78 | -1 | d | none | deleted by RBM2D T2274 (dead code of the final d=2 proof, commit 99d6fe0) |  |
| SpectralAlgebra.lean | 62 | 53 | a | RBM3D/Gauss/SpectralAlgebra.lean | no exponent token; renaming R1-R4 only (lattice tokens 0, Sizes tokens 0) |  |
| SpectralDerivative.lean | 49 | 32 | a | RBM3D/Gauss/SpectralDerivative.lean | no exponent token; renaming R1-R4 only (lattice tokens 0, Sizes tokens 0) |  |
| SpectralWindow.lean | 81 | 50 | a | RBM3D/Gauss/SpectralWindow.lean | no exponent token; renaming R1-R4 only (lattice tokens 1, Sizes tokens 0) |  |
| Stein.lean | 265 | 243 | d | RBM3D/Gauss/Stein.lean | superseded by merged RBM3D |  |
| SteinConcrete.lean | 138 | -1 | d | none | deleted by RBM2D T2274 (dead code of the final d=2 proof, commit 99d6fe0) |  |
| SteinMatrix.lean | 223 | 198 | a | RBM3D/Gauss/SteinMatrix.lean | resampling/Stein for a countable product measure; merged SteinMatrix.lean covers the finite-pi part |  |

### Green -> RBM3D/Green

| RBM2D file | lines c9a24cf | kept 0c1330a | class | RBM3D target | basis | labels (this paper) |
|---|---|---|---|---|---|---|
| AvgPins.lean | 736 | 567 | b | RBM3D/Green/AvgPins.lean | exponent tokens 9 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | GavLGEX@3_5:33; lem_GbEXP@3_5:14 |
| CondDom.lean | 647 | 359 | b | RBM3D/Green/CondDom.lean | exponent tokens 9 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | lem_GbEXP@3_5:14, lem_ConArg@3_5:42 (dir default) |
| CondRow.lean | 492 | 373 | a | RBM3D/Green/CondRow.lean | no exponent token; renaming R1-R4 only (lattice tokens 57, Sizes tokens 233) | lem_GbEXP@3_5:14, lem_ConArg@3_5:42 (dir default) |
| CondStable.lean | 645 | 433 | b | RBM3D/Green/CondStable.lean | exponent tokens 2 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | lem_GbEXP@3_5:14, lem_ConArg@3_5:42 (dir default) |
| EntryBlock.lean | 836 | 557 | b | RBM3D/Green/EntryBlock.lean | exponent tokens 51 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | lem_GbEXP@3_5:14; example@A:548 |
| EntryCore.lean | 1014 | 856 | a | RBM3D/Green/EntryCore.lean | no exponent token; renaming R1-R4 only (lattice tokens 0, Sizes tokens 0) | lem_GbEXP@3_5:14, lem_ConArg@3_5:42 (dir default) |
| EntryDom.lean | 1042 | 641 | b | RBM3D/Green/EntryDom.lean | exponent tokens 9 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | lem_GbEXP@3_5:14; GavLGEX@3_5:33; GiiGEX@3_5:21; GijGEX@3_5:24; def_asGMc@3_5:16 |
| EntryGauss.lean | 151 | 108 | a | RBM3D/Green/EntryGauss.lean | no exponent token; renaming R1-R4 only (lattice tokens 0, Sizes tokens 4) | GiiGEX@3_5:21; GijGEX@3_5:24 |
| Eq45Small.lean | 505 | 415 | b | RBM3D/Green/Eq45Small.lean | exponent tokens 2 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | def_asGMc@3_5:16 |
| FlucAvg.lean | 546 | 411 | b | RBM3D/Green/FlucAvg.lean | exponent tokens 11 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | GavLGEX@3_5:33; Main_DEL_COND@1_2:359 |
| FlucAvgDet.lean | 623 | 524 | b | RBM3D/Green/FlucAvgDet.lean | exponent tokens 24 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | GavLGEX@3_5:33; lem_GbEXP@3_5:14 |
| FlucIter.lean | 1877 | 1540 | b | RBM3D/Green/FlucIter.lean | exponent tokens 9 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | GavLGEX@3_5:33 |
| FlucIterHigh.lean | 970 | 764 | b | RBM3D/Green/FlucIterHigh.lean | exponent tokens 1 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | GavLGEX@3_5:33 |
| FlucThreshold.lean | 718 | 477 | b | RBM3D/Green/FlucThreshold.lean | exponent tokens 8 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | lem_GbEXP@3_5:14, lem_ConArg@3_5:42 (dir default) |
| FlucVanish.lean | 556 | 477 | b | RBM3D/Green/FlucVanish.lean | exponent tokens 29 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | GavLGEX@3_5:33 |
| GbEXP.lean | 111 | 59 | b | RBM3D/Green/GbEXP.lean | exponent tokens 2 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | GavLGEX@3_5:33; GiiGEX@3_5:21; GijGEX@3_5:24; lem_GbEXP@3_5:14 |
| GreenDeriv.lean | 418 | 356 | a | RBM3D/Green/GreenDeriv.lean | no exponent token; renaming R1-R4 only (lattice tokens 16, Sizes tokens 55) | lem_GbEXP@3_5:14, lem_ConArg@3_5:42 (dir default) |
| IBP.lean | 1653 | 1268 | b | RBM3D/Green/IBP.lean | exponent tokens 6 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | GavLGEX@3_5:33 |
| IBPDet.lean | 335 | 287 | b | RBM3D/Green/IBPDet.lean | exponent tokens 9 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | GavLGEX@3_5:33 |
| IBPPoly.lean | 482 | 392 | a | RBM3D/Green/IBPPoly.lean | no exponent token; renaming R1-R4 only (lattice tokens 5, Sizes tokens 103) | lem_GbEXP@3_5:14, lem_ConArg@3_5:42 (dir default) |
| IBPRem.lean | 886 | 542 | b | RBM3D/Green/IBPRem.lean | exponent tokens 3 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | GavLGEX@3_5:33; Main_DEL_COND@1_2:359 |
| LDE.lean | 818 | 712 | b | RBM3D/Green/LDE.lean | exponent tokens 6 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | lem_GbEXP@3_5:14, lem_ConArg@3_5:42 (dir default) |
| LDEQuad.lean | 1105 | 924 | b | RBM3D/Green/LDEQuad.lean | exponent tokens 1 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | lem_GbEXP@3_5:14, lem_ConArg@3_5:42 (dir default) |
| LDEQuadInst.lean | 794 | 701 | a | RBM3D/Green/LDEQuadInst.lean | no exponent token; renaming R1-R4 only (lattice tokens 94, Sizes tokens 324) | lem_GbEXP@3_5:14, lem_ConArg@3_5:42 (dir default) |
| LDEQuadMom.lean | 970 | 796 | a | RBM3D/Green/LDEQuadMom.lean | no exponent token; renaming R1-R4 only (lattice tokens 6, Sizes tokens 165) | lem_GbEXP@3_5:14, lem_ConArg@3_5:42 (dir default) |
| LDEQuadT.lean | 1209 | 1019 | a | RBM3D/Green/LDEQuadT.lean | no exponent token; renaming R1-R4 only (lattice tokens 6, Sizes tokens 148) | lem_GbEXP@3_5:14 |
| LocalLaw.lean | 378 | 352 | b | RBM3D/Green/LocalLaw.lean | exponent tokens 13 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | GavLGEX@3_5:33; GijGEX@3_5:24 |
| Minor.lean | 317 | 225 | a | RBM3D/Green/Minor.lean | no exponent token; renaming R1-R4 only (lattice tokens 2, Sizes tokens 0) | lem_GbEXP@3_5:14, lem_ConArg@3_5:42 (dir default) |
| MinorDiff.lean | 1388 | 917 | b | RBM3D/Green/MinorDiff.lean | exponent tokens 1 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | GavLGEX@3_5:33; def_asGMc@3_5:16 |
| MinorDiffCond.lean | 1464 | 912 | b | RBM3D/Green/MinorDiffCond.lean | exponent tokens 3 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | def_asGMc@3_5:16; lem_GbEXP@3_5:14 |
| MinorGoodLe.lean | 474 | 336 | b | RBM3D/Green/MinorGoodLe.lean | exponent tokens 1 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | def_asGMc@3_5:16 |
| Pins.lean | 593 | 342 | b | RBM3D/Green/Pins.lean | exponent tokens 5 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | GavLGEX@3_5:33; GiiGEX@3_5:21; GijGEX@3_5:24; def_asGMc@3_5:16; lem_GbEXP@3_5:14; Eq:Gdecay_w@1_2:1349; Gtmwc@1_2:1327; Main_DEL_COND@1_2:359 |
| RowIndep.lean | 1759 | 1313 | b | RBM3D/Green/RowIndep.lean | exponent tokens 1 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | lem_GbEXP@3_5:14, lem_ConArg@3_5:42 (dir default) |
| Stability.lean | 415 | 363 | c | RBM3D/Green/Stability.lean (re-written) | Kstab2 = O(1+log L) is a d=2 lattice sum; d>=3 stability constant differs | lem_propTH(4)@1_2:1140, eq:THETAinftinf@1_2:1141, eq:latticesum_d3 (merged Kernel/SumDecay.lean) |

### Hierarchy -> RBM3D/Hierarchy

| RBM2D file | lines c9a24cf | kept 0c1330a | class | RBM3D target | basis | labels (this paper) |
|---|---|---|---|---|---|---|
| ContractionBasic.lean | 72 | 72 | b | RBM3D/Hierarchy/ContractionBasic.lean | exponent tokens 7 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) |
| ContractionCutWords.lean | 117 | 117 | b | RBM3D/Hierarchy/ContractionCutWords.lean | exponent tokens 1 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) |
| ContractionDirections.lean | 198 | 181 | b | RBM3D/Hierarchy/ContractionDirections.lean | exponent tokens 2 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) |
| ContractionDrift.lean | 81 | 81 | b | RBM3D/Hierarchy/ContractionDrift.lean | exponent tokens 6 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) |
| ContractionEdgeSplits.lean | 66 | 51 | a | RBM3D/Hierarchy/ContractionEdgeSplits.lean | no exponent token; renaming R1-R4 only (lattice tokens 2, Sizes tokens 0) | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) |
| ContractionFirstDerivativePositionSum.lean | 77 | 77 | a | RBM3D/Hierarchy/ContractionFirstDerivativePositionSum.lean | no exponent token; renaming R1-R4 only (lattice tokens 17, Sizes tokens 0) | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) |
| ContractionPairPositionCut.lean | 80 | 53 | b | RBM3D/Hierarchy/ContractionPairPositionCut.lean | exponent tokens 2 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) |
| ContractionPairSplits.lean | 107 | 49 | a | RBM3D/Hierarchy/ContractionPairSplits.lean | no exponent token; renaming R1-R4 only (lattice tokens 0, Sizes tokens 0) | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) |
| ContractionPositionLoopBridge.lean | 80 | 46 | a | RBM3D/Hierarchy/ContractionPositionLoopBridge.lean | no exponent token; renaming R1-R4 only (lattice tokens 10, Sizes tokens 0) | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) |
| ContractionSameEdgePositionCut.lean | 69 | 47 | b | RBM3D/Hierarchy/ContractionSameEdgePositionCut.lean | exponent tokens 2 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) |
| ContractionSecondDerivativePositionSum.lean | 151 | 151 | a | RBM3D/Hierarchy/ContractionSecondDerivativePositionSum.lean | no exponent token; renaming R1-R4 only (lattice tokens 35, Sizes tokens 0) | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) |
| ContractionSecondDerivativeTraceSum.lean | 52 | 52 | a | RBM3D/Hierarchy/ContractionSecondDerivativeTraceSum.lean | no exponent token; renaming R1-R4 only (lattice tokens 3, Sizes tokens 0) | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) |
| ContractionSecondLoop.lean | 201 | 201 | b | RBM3D/Hierarchy/ContractionSecondLoop.lean | exponent tokens 3 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) |
| ContractionSecondLoopAllCuts.lean | 111 | 81 | b | RBM3D/Hierarchy/ContractionSecondLoopAllCuts.lean | exponent tokens 9 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) |
| ContractionSecondLoopExpectedCuts.lean | 358 | -1 | d | none | deleted by RBM2D T2274 (dead code of the final d=2 proof, commit 99d6fe0) |  |
| ContractionSecondLoopPositionSum.lean | 48 | -1 | d | none | deleted by RBM2D T2274 (dead code of the final d=2 proof, commit 99d6fe0) |  |
| ContractionSecondLoopReverse.lean | 42 | -1 | d | none | deleted by RBM2D T2274 (dead code of the final d=2 proof, commit 99d6fe0) |  |
| ContractionSecondLoopSameEdge.lean | 129 | 65 | b | RBM3D/Hierarchy/ContractionSecondLoopSameEdge.lean | exponent tokens 3 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) |
| ContractionSecondLoopSameEdgeCut.lean | 72 | 72 | b | RBM3D/Hierarchy/ContractionSecondLoopSameEdgeCut.lean | exponent tokens 1 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) |
| ContractionSecondLoopSameEdgeWord.lean | 86 | 86 | b | RBM3D/Hierarchy/ContractionSecondLoopSameEdgeWord.lean | exponent tokens 1 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) |
| ContractionSum.lean | 214 | 214 | b | RBM3D/Hierarchy/ContractionSum.lean | exponent tokens 2 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) |
| ContractionUnused.lean | 120 | 120 | b | RBM3D/Hierarchy/ContractionUnused.lean | exponent tokens 1 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) |
| LoopHierarchyCutBlockSumBound.lean | 118 | 31 | b | RBM3D/Hierarchy/LoopHierarchyCutBlockSumBound.lean | exponent tokens 1 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) |
| LoopHierarchyCutContinuity.lean | 321 | 69 | b | RBM3D/Hierarchy/LoopHierarchyCutContinuity.lean | exponent tokens 5 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) |
| LoopHierarchyCutLengths.lean | 151 | -1 | d | none | deleted by RBM2D T2274 (dead code of the final d=2 proof, commit 99d6fe0) |  |
| LoopHierarchyCutNormBounds.lean | 169 | -1 | d | none | deleted by RBM2D T2274 (dead code of the final d=2 proof, commit 99d6fe0) |  |
| LoopHierarchyCutTotalBound.lean | 131 | -1 | d | none | unreachable from Main/Endpoints.lean + Main/BUnivHolds.lean (import closure) |  |
| LoopHierarchyDerivativeBound.lean | 87 | -1 | d | none | unreachable from Main/Endpoints.lean + Main/BUnivHolds.lean (import closure) |  |
| LoopHierarchyEnvelopeLabelSum.lean | 165 | -1 | d | none | unreachable from Main/Endpoints.lean + Main/BUnivHolds.lean (import closure) |  |
| LoopHierarchyFirstDuhamel.lean | 59 | -1 | d | none | deleted by RBM2D T2274 (dead code of the final d=2 proof, commit 99d6fe0) |  |
| LoopHierarchyFromInitialBound.lean | 89 | -1 | d | none | unreachable from Main/Endpoints.lean + Main/BUnivHolds.lean (import closure) |  |
| LoopHierarchyGenerator.lean | 93 | -1 | d | none | deleted by RBM2D T2274 (dead code of the final d=2 proof, commit 99d6fe0) |  |
| LoopHierarchyInitialAverageBound.lean | 90 | -1 | d | none | unreachable from Main/Endpoints.lean + Main/BUnivHolds.lean (import closure) |  |
| LoopHierarchyIntegral.lean | 88 | -1 | d | none | deleted by RBM2D T2274 (dead code of the final d=2 proof, commit 99d6fe0) |  |
| LoopHierarchyIntegralBound.lean | 86 | -1 | d | none | unreachable from Main/Endpoints.lean + Main/BUnivHolds.lean (import closure) |  |
| LoopHierarchyIntegralZero.lean | 87 | -1 | d | none | deleted by RBM2D T2274 (dead code of the final d=2 proof, commit 99d6fe0) |  |
| LoopHierarchyLengthEnvelopeMonotone.lean | 91 | -1 | d | none | unreachable from Main/Endpoints.lean + Main/BUnivHolds.lean (import closure) |  |
| LoopHierarchyLengthEnvelopeSmall.lean | 101 | -1 | d | none | unreachable from Main/Endpoints.lean + Main/BUnivHolds.lean (import closure) |  |
| LoopHierarchyOneEdge.lean | 99 | -1 | d | none | deleted by RBM2D T2274 (dead code of the final d=2 proof, commit 99d6fe0) |  |
| LoopHierarchyRHSBound.lean | 113 | -1 | d | none | unreachable from Main/Endpoints.lean + Main/BUnivHolds.lean (import closure) |  |
| LoopHierarchySpectralCutBounds.lean | 159 | -1 | d | none | unreachable from Main/Endpoints.lean + Main/BUnivHolds.lean (import closure) |  |
| LoopHierarchyTwoEdge.lean | 110 | -1 | d | none | deleted by RBM2D T2274 (dead code of the final d=2 proof, commit 99d6fe0) |  |
| Loops.lean | 275 | 267 | b | RBM3D/Hierarchy/Loops.lean | exponent tokens 15 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Def:G_loop@1_2:811 |
| Operations.lean | 99 | 81 | a | RBM3D/Hierarchy/Operations.lean | single-edge cut-and-glue `cutGlue` of Def:oper_loop on LoopIdx (Operations.lean:27); merged TreeRep has only cutGlueL/R | Def:oper_loop@1_2:905 |
| OperationsPair.lean | 71 | 71 | d | RBM3D/Loop/TreeRep.lean (LoopIdx.cutGlueL, cutGlueR) | superseded by merged RBM3D | Def:oper_loop@1_2:905 |
| OperationsPairWord.lean | 142 | 142 | a | RBM3D/Hierarchy/OperationsPairWord.lean | no exponent token; renaming R1-R4 only (lattice tokens 23, Sizes tokens 0) | Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949 (dir default) |
| WardResolvent.lean | 193 | 162 | b | RBM3D/Hierarchy/WardResolvent.lean | exponent tokens 11 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | WI_calL@1_2:1036 |

### Induction -> RBM3D/Induction

| RBM2D file | lines c9a24cf | kept 0c1330a | class | RBM3D target | basis | labels (this paper) |
|---|---|---|---|---|---|---|
| AltAbsorb.lean | 1048 | 983 | b | RBM3D/Induction/AltAbsorb.lean | exponent tokens 52 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| AltBudget.lean | 788 | 674 | b | RBM3D/Induction/AltBudget.lean | exponent tokens 11 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| AltBudgetTerms.lean | 698 | 281 | b | RBM3D/Induction/AltBudgetTerms.lean | exponent tokens 18 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| AltDriftQ.lean | 2865 | 1950 | b | RBM3D/Induction/AltDriftQ.lean | exponent tokens 69 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | int_K-L+QE@6:109; jywiiwsoks@3_5:1271 |
| AltEnd.lean | 1873 | 975 | b | RBM3D/Induction/AltEnd.lean | exponent tokens 8 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | int_K-L+QE@6:109; jywiiwsoks@3_5:1271; lem:STOeq_Qt@3_5:1364 |
| AltEndCompose.lean | 1072 | 1072 | b | RBM3D/Induction/AltEndCompose.lean | exponent tokens 11 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| AltGridQ.lean | 2384 | 2275 | b | RBM3D/Induction/AltGridQ.lean | exponent tokens 66 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Def:QtPt@3_5:1204; int_K-L+Q@3_5:1337; zjuii2@3_5:1318 |
| AltLevelsE.lean | 551 | 454 | b | RBM3D/Induction/AltLevelsE.lean | no exponent token but 6 uses of the d=2 scales (scaleM, ellT, tailT, Meta, ellz): replace by ell_t (eq:ellt), B_{t,K} (eq_B_param), W^{-d}B_{t,0} | int_K-L+QE@6:109; lem:STOeq_NQ@3_5:1136; lem:STOeq_Qt@3_5:1364 |
| AltLevelsQ.lean | 1043 | 946 | b | RBM3D/Induction/AltLevelsQ.lean | exponent tokens 14 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | jywiiwsoks@3_5:1271; lem:STOeq_Qt@3_5:1364; lem_+Q@3_5:1285; normQA@3_5:1287 |
| AltLevelsQ0.lean | 791 | 737 | b | RBM3D/Induction/AltLevelsQ0.lean | exponent tokens 34 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| AltProxyQ.lean | 1632 | 1265 | b | RBM3D/Induction/AltProxyQ.lean | exponent tokens 51 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Def:QtPt@3_5:1204; lem_+Q@3_5:1285; normQA@3_5:1287 |
| AltSymm.lean | 483 | 407 | b | RBM3D/Induction/AltSymm.lean | exponent tokens 6 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Kn2sol@1_2:1175 |
| AzumaProxyN.lean | 2469 | 1540 | b | RBM3D/Induction/AzumaProxyN.lean | exponent tokens 16 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | alu9_STime@3_5:229; example@A:548 |
| B45.lean | 2095 | 1196 | b | RBM3D/Induction/B45.lean | exponent tokens 106 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | jywiiwsoks@3_5:1271; lem_WI_K@1_2:1034; prop:ThfadC@1_2:1144; res_decayLK@3_5:1128 |
| BcalE.lean | 2214 | 2044 | b | RBM3D/Induction/BcalE.lean | exponent tokens 51 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | DefKsimLK@3_5:89; GavLGEX@3_5:33; def:CALE@3_5:169; def_ELKLK@3_5:97; def_EwtG@1_2:961 |
| BcalEDecay.lean | 1314 | 1153 | b | RBM3D/Induction/BcalEDecay.lean | exponent tokens 66 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Def_decay@3_5:1115; lem_decayLoop@3_5:1126 |
| Chain.lean | 454 | 424 | b | RBM3D/Induction/Chain.lean | exponent tokens 3 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | ML:GLoop@1_2:1193; ML:GLoop_expec@1_2:1203; ML:GtLocal@1_2:1217; lem:main_ind@1_2:1256; Eq:L-KGt2@1_2:1197; Kn2sol@1_2:1175; ML:Kbound@1_2:1054 |
| ConArg.lean | 807 | 767 | b | RBM3D/Induction/ConArg.lean | exponent tokens 8 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | lem_ConArg@3_5:42; res_lo_bo_eta@3_5:52 |
| ConArgDet.lean | 1348 | 966 | b | RBM3D/Induction/ConArgDet.lean | exponent tokens 55 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | lem_ConArg@3_5:42 |
| Continuity.lean | 1644 | 1462 | b | RBM3D/Induction/Continuity.lean | exponent tokens 49 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Gtmwc@1_2:1327; lRB1@1_2:1321 |
| DecayLoop.lean | 934 | 816 | b | RBM3D/Induction/DecayLoop.lean | exponent tokens 4 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | GijGEX@3_5:24; lem_decayLoop@3_5:1126; res_decayLK@3_5:1128; Kn2sol@1_2:1175 |
| Defs.lean | 453 | 326 | b | RBM3D/Induction/Defs.lean | no exponent token but 23 uses of the d=2 scales (scaleM, ellT, tailT, Meta, ellz): replace by ell_t (eq:ellt), B_{t,K} (eq_B_param), W^{-d}B_{t,0} | ML:GLoop@1_2:1193; ML:GLoop_expec@1_2:1203; ML:GtLocal@1_2:1217; lem:main_ind@1_2:1256; Def_Ktza@1_2:986; Def_decay@3_5:1115; Eq:Gdecay@1_2:1205; Eq:Gdecay+IND@1_2:1267 |
| GridAssemblyN.lean | 1761 | 1171 | b | RBM3D/Induction/GridAssemblyN.lean | exponent tokens 4 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | alu9_STime@3_5:229; example@A:548; int_K-L_ST@3_5:136 |
| GridDriftN.lean | 911 | 850 | b | RBM3D/Induction/GridDriftN.lean | exponent tokens 32 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | def_Ustz@3_5:116; pro_dyncalK@1_2:990 |
| GridDuhamelN.lean | 510 | 235 | b | RBM3D/Induction/GridDuhamelN.lean | exponent tokens 2 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | alu9_STime@3_5:229; def_Ustz@3_5:116; int_K-L_ST@3_5:136 |
| GridEnvelopeN.lean | 713 | 580 | b | RBM3D/Induction/GridEnvelopeN.lean | exponent tokens 12 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | int_K-L_ST@3_5:136 |
| GridGoodEvent.lean | 852 | 764 | b | RBM3D/Induction/GridGoodEvent.lean | exponent tokens 22 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | lem:STOeq_NQ@3_5:1136; lem:STOeq_Qt@3_5:1364; lem_decayLoop@3_5:1126; example@A:548 |
| GridGoodN.lean | 1711 | 1074 | b | RBM3D/Induction/GridGoodN.lean | exponent tokens 2 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | alu9_STime@3_5:229; def:CALE@3_5:169; int_K-L_ST@3_5:136; lem:DIfREP@3_5:218; lem:STOeq_NQ@3_5:1136; lem:STOeq_Qt@3_5:1364; lem_decayLoop@3_5:1126; example@A:548 |
| HierAlgebra.lean | 787 | 704 | b | RBM3D/Induction/HierAlgebra.lean | exponent tokens 37 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | DefKsimLK@3_5:89; DefTHUST@3_5:109; def_ELKLK@3_5:97; pro_dyncalK@1_2:990; eq_L-Keee@3_5:73 |
| HierVocab.lean | 664 | 444 | b | RBM3D/Induction/HierVocab.lean | exponent tokens 25 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Def:QtPt@3_5:1204; DefKsimLK@3_5:89; DefTHUST@3_5:109; def:CALE@3_5:169; def_ELKLK@3_5:97; def_EwtG@1_2:961; alu9_STime@3_5:229; def_diffakn_k@3_5:187 |
| HierarchyN.lean | 76 | 38 | a | RBM3D/Induction/HierarchyN.lean | no exponent token; renaming R1-R4 only (lattice tokens 5, Sizes tokens 0) |  |
| KcalDecay.lean | 913 | 841 | b | RBM3D/Induction/KcalDecay.lean | exponent tokens 23 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | eq:bcal_k@1_2:1056; lem_decayLoop@3_5:1126; Kn2sol@1_2:1175 |
| LocalFormCalc.lean | 3861 | 3340 | b | RBM3D/Induction/LocalFormCalc.lean | exponent tokens 116 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Def:QtPt@3_5:1204; lem:sum_decay@3_5:1632; eq:bcal_k@1_2:1056 |
| LocalFormCuts.lean | 2296 | 2120 | b | RBM3D/Induction/LocalFormCuts.lean | exponent tokens 40 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | res_decayLK@3_5:1128 |
| LocalFormLin.lean | 547 | 498 | b | RBM3D/Induction/LocalFormLin.lean | exponent tokens 25 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Def:QtPt@3_5:1204 |
| LoopC2N.lean | 580 | 475 | b | RBM3D/Induction/LoopC2N.lean | exponent tokens 9 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | example@A:548 |
| LoopGenN.lean | 574 | 536 | b | RBM3D/Induction/LoopGenN.lean | exponent tokens 11 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | def_EwtG@1_2:961; eq:mainStoflow@1_2:951 |
| MainInd.lean | 237 | 168 | b | RBM3D/Induction/MainInd.lean | no exponent token but 1 uses of the d=2 scales (scaleM, ellT, tailT, Meta, ellz): replace by ell_t (eq:ellt), B_{t,K} (eq_B_param), W^{-d}B_{t,0} | ML:GLoop@1_2:1193; ML:GLoop_expec@1_2:1203; ML:GtLocal@1_2:1217; lem:main_ind@1_2:1256 |
| NonAltBudget.lean | 1475 | 852 | b | RBM3D/Induction/NonAltBudget.lean | exponent tokens 14 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| NonAltEnd.lean | 1690 | 1287 | b | RBM3D/Induction/NonAltEnd.lean | exponent tokens 16 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | lem:STOeq_NQ@3_5:1136; example@A:548 |
| NonAltGood.lean | 2308 | 830 | b | RBM3D/Induction/NonAltGood.lean | exponent tokens 87 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | alu9_STime@3_5:229; int_K-L+Q@3_5:1337; lem:STOeq_NQ@3_5:1136 |
| PPClosure.lean | 1159 | 1070 | b | RBM3D/Induction/PPClosure.lean | exponent tokens 57 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| PPCondVar.lean | 519 | 413 | b | RBM3D/Induction/PPCondVar.lean | exponent tokens 46 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | alu9_STime@3_5:229; def:CALE@3_5:169 |
| PPDrift.lean | 887 | 513 | b | RBM3D/Induction/PPDrift.lean | exponent tokens 65 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | def_ELKLK@3_5:97; def_EwtG@1_2:961; example@A:548 |
| PPGoodEvent.lean | 1033 | 946 | b | RBM3D/Induction/PPGoodEvent.lean | exponent tokens 7 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | GavLGEX@3_5:33; lem_GbEXP@3_5:14; lem_decayLoop@3_5:1126; example@A:548 |
| PPKernel.lean | 346 | 313 | b | RBM3D/Induction/PPKernel.lean | exponent tokens 4 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | def_Ustz@3_5:116; prop:ThfadC@1_2:1144 |
| PPVocab.lean | 2026 | 1199 | b | RBM3D/Induction/PPVocab.lean | exponent tokens 15 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | alu9_STime@3_5:229; int_K-L_ST@3_5:136; lRB1@1_2:1321 |
| PerTimeCalc.lean | 1434 | 615 | a | RBM3D/Induction/PerTimeCalc.lean | no exponent token; renaming R1-R4 only (lattice tokens 1, Sizes tokens 0) |  |
| QVN.lean | 738 | 704 | b | RBM3D/Induction/QVN.lean | exponent tokens 17 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | def:CALE@3_5:169; defEOTE@3_5:176; def_diffakn_k@3_5:187 |
| QopBounds.lean | 747 | 673 | b | RBM3D/Induction/QopBounds.lean | exponent tokens 42 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | lem_+Q@3_5:1285; normQA@3_5:1287 |
| Region.lean | 104 | -1 | d | none | unreachable from Main/Endpoints.lean + Main/BUnivHolds.lean (import closure) |  |
| ScaleFacts.lean | 419 | 312 | c | RBM3D/Induction/ScaleFacts.lean (re-written) | scale facts on M_u (d=2); redo on W^{-d}B_{t,0} | con_st_ind@1_2:1296, eq:ellt@1_2:1121, eq_B_param@1_2:1107; con_st_ind@1_2:1296 |
| Split.lean | 952 | 818 | b | RBM3D/Induction/Split.lean | exponent tokens 24 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| Step1.lean | 1515 | 1384 | b | RBM3D/Induction/Step1.lean | exponent tokens 27 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Gtmwc@1_2:1327; con_st_ind@1_2:1296; lRB1@1_2:1321; lem:main_ind@1_2:1256; lem_GbEXP@3_5:14; GijGEX@3_5:24; ML:Kbound@1_2:1054; lem_ConArg@3_5:42 |
| Step2TargetV3.lean | 73 | 43 | c | RBM3D/Induction/Step2TargetV3.lean (re-written) | Step 2 target pin (route (D) near exponent 3): re-pin for d>=3 | eq:def2_stopping@3_5:533, Gronwall_inequality@3_5:493, eq:Gronwall_dervJuD@3_5:529, defCALJ@3_5:365, lem:newKLK@3_5:371, lem:LWterm@3_5:385, lem: EMn2_N@3_5:427, Eq:Gdecay_w@1_2:1349; Eq:Gdecay_w@1_2:1349; Gt_bound_flow@1_2:1342 |
| Step3.lean | 1925 | 1805 | b | RBM3D/Induction/Step3.lean | exponent tokens 10 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Eq:Gdecay_w@1_2:1349; Eq:LGxb@1_2:1361; Gt_bound+IND@1_2:1276; Gt_bound_flow@1_2:1342; lem:main_ind@1_2:1256; lRB1@1_2:1321 |
| Step45.lean | 1445 | 1318 | b | RBM3D/Induction/Step45.lean | exponent tokens 5 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Eq:Gdecay_flow@1_2:1380; Eq:L-KGt-flow@1_2:1371; GavLGEX@3_5:33; lem:main_ind@1_2:1256 |
| StepDecompN.lean | 1550 | 1154 | b | RBM3D/Induction/StepDecompN.lean | exponent tokens 4 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | alu9_STime@3_5:229; int_K-L_ST@3_5:136 |
| StoppedEndDefs.lean | 1082 | 686 | b | RBM3D/Induction/StoppedEndDefs.lean | exponent tokens 7 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | lem:STOeq_NQ@3_5:1136; lem:STOeq_Qt@3_5:1364; NALsigm@3_5:1138; int_K-L+QE@6:109; jywiiwsoks@3_5:1271; lem:sum_decay@3_5:1632 |
| SumZeroQ.lean | 455 | 390 | b | RBM3D/Induction/SumZeroQ.lean | exponent tokens 2 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Def:QtPt@3_5:1204 |

### Main -> RBM3D/Main

| RBM2D file | lines c9a24cf | kept 0c1330a | class | RBM3D target | basis | labels (this paper) |
|---|---|---|---|---|---|---|
| BUniv.lean | 71 | 46 | a | RBM3D/Main/BUniv.lean | no exponent token; renaming R1-R4 only (lattice tokens 0, Sizes tokens 2) | MR:decol@1_2:357, MR:locSC@1_2:386, MR:QUE@1_2:406, MR:QuDiff@1_2:488 (dir default) |
| BUnivHolds.lean | 76 | 62 | a | RBM3D/Main/BUnivHolds.lean | no exponent token; renaming R1-R4 only (lattice tokens 0, Sizes tokens 3) | eq:universality@1_2:454 |
| DecolFromLocal.lean | 361 | 341 | b | RBM3D/Main/DecolFromLocal.lean | exponent tokens 17 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | MR:decol@1_2:357; MR:locSC@1_2:386 |
| Endpoints.lean | 71 | 62 | b | RBM3D/Main/Endpoints.lean | no exponent token but 1 uses of the d=2 scales (scaleM, ellT, tailT, Meta, ellz): replace by ell_t (eq:ellt), B_{t,K} (eq_B_param), W^{-d}B_{t,0} | MR:QUE@1_2:406; MR:decol@1_2:357; MR:locSC@1_2:386 |
| EndpointsFromSTO.lean | 811 | 625 | b | RBM3D/Main/EndpointsFromSTO.lean | no exponent token but 40 uses of the d=2 scales (scaleM, ellT, tailT, Meta, ellz): replace by ell_t (eq:ellt), B_{t,K} (eq_B_param), W^{-d}B_{t,0} | MR:locSC@1_2:386; G_bound@1_2:388; G_bound_ave@1_2:391 |
| P7FromSTO.lean | 183 | 183 | b | RBM3D/Main/P7FromSTO.lean | no exponent token but 1 uses of the d=2 scales (scaleM, ellT, tailT, Meta, ellz): replace by ell_t (eq:ellt), B_{t,K} (eq_B_param), W^{-d}B_{t,0} | ML:GLoop@1_2:1193 |
| QUEFromQDiff.lean | 1084 | 1069 | b | RBM3D/Main/QUEFromQDiff.lean | exponent tokens 57 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | MR:QUE@1_2:406; Meq:QdS1@1_2:504; Meq:QdS2@1_2:507; prop:BD1@1_2:1153; ssfa2@1_2:524; Meq:QUE@1_2:411; Meq:QUE2@1_2:417 |
| RegionUnif.lean | 950 | -1 | b | RBM3D/Main/RegionUnif.lean | deleted by RBM2D T2274 as dead code (same reason); needed for the same purpose: union over the spectral region inside P | MR:decol@1_2:357, MR:locSC@1_2:386, MR:QUE@1_2:406, MR:QuDiff@1_2:488 (dir default) |
| ZRescale.lean | 459 | 459 | b | RBM3D/Main/ZRescale.lean | exponent tokens 15 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | MR:locSC@1_2:386; zztE@1_2:787; G_bound_ave@1_2:391; Kn2sol@1_2:1175; eq:zztE@1_2:791 |

### Path -> RBM3D/Path

| RBM2D file | lines c9a24cf | kept 0c1330a | class | RBM3D target | basis | labels (this paper) |
|---|---|---|---|---|---|---|
| Azuma.lean | 339 | 235 | a | RBM3D/Path/Azuma.lean | generic Azuma/Doob on any probability space |  |
| Bootstrap.lean | 419 | 315 | c | RBM3D/Path/Bootstrap.lean (re-written) | Step 2 stopping/Gronwall argument is d>=3-specific (DECISIONS §7) | eq:def2_stopping@3_5:533, Gronwall_inequality@3_5:493, eq:Gronwall_dervJuD@3_5:529, defCALJ@3_5:365, lem:newKLK@3_5:371, lem:LWterm@3_5:385, lem: EMn2_N@3_5:427, Eq:Gdecay_w@1_2:1349; Eq:Gdecay_w@1_2:1349; def_WTuD@3_5:2297; Main_DEL_COND@1_2:359 |
| DriftAlgebra.lean | 634 | 602 | b | RBM3D/Path/DriftAlgebra.lean | exponent tokens 24 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | DefTHUST@3_5:109; Kn2sol@1_2:1175; def_ELKLK@3_5:97; def_EwtG@1_2:961; eq:mainStoflow@1_2:951; eq_L-Keee@3_5:73; pro_dyncalK@1_2:990 |
| DriftLip.lean | 693 | 91 | b | RBM3D/Path/DriftLip.lean | exponent tokens 60 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| DriftPoint.lean | 559 | 478 | c | RBM3D/Path/DriftPoint.lean (re-written) | Step 2 stopping/Gronwall argument is d>=3-specific (DECISIONS §7) | eq:def2_stopping@3_5:533, Gronwall_inequality@3_5:493, eq:Gronwall_dervJuD@3_5:529, defCALJ@3_5:365, lem:newKLK@3_5:371, lem:LWterm@3_5:385, lem: EMn2_N@3_5:427, Eq:Gdecay_w@1_2:1349 |
| DuhamelTail.lean | 967 | 654 | b | RBM3D/Path/DuhamelTail.lean | exponent tokens 2 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | alu9_STime@3_5:229 |
| Expansion.lean | 1159 | 978 | b | RBM3D/Path/Expansion.lean | exponent tokens 19 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | int_K-L_ST@3_5:136 |
| GoodEvent.lean | 1183 | 1037 | c | RBM3D/Path/GoodEvent.lean (re-written) | Step 2 stopping/Gronwall argument is d>=3-specific (DECISIONS §7) | eq:def2_stopping@3_5:533, Gronwall_inequality@3_5:493, eq:Gronwall_dervJuD@3_5:529, defCALJ@3_5:365, lem:newKLK@3_5:371, lem:LWterm@3_5:385, lem: EMn2_N@3_5:427, Eq:Gdecay_w@1_2:1349; Eq:Gdecay+IND@1_2:1267 |
| GoodEventClose.lean | 1393 | 1241 | c | RBM3D/Path/GoodEventClose.lean (re-written) | Step 2 stopping/Gronwall argument is d>=3-specific (DECISIONS §7) | eq:def2_stopping@3_5:533, Gronwall_inequality@3_5:493, eq:Gronwall_dervJuD@3_5:529, defCALJ@3_5:365, lem:newKLK@3_5:371, lem:LWterm@3_5:385, lem: EMn2_N@3_5:427, Eq:Gdecay_w@1_2:1349 |
| GoodEventGrid.lean | 1336 | 1153 | c | RBM3D/Path/GoodEventGrid.lean (re-written) | Step 2 stopping/Gronwall argument is d>=3-specific (DECISIONS §7) | eq:def2_stopping@3_5:533, Gronwall_inequality@3_5:493, eq:Gronwall_dervJuD@3_5:529, defCALJ@3_5:365, lem:newKLK@3_5:371, lem:LWterm@3_5:385, lem: EMn2_N@3_5:427, Eq:Gdecay_w@1_2:1349 |
| GoodSet.lean | 873 | 847 | c | RBM3D/Path/GoodSet.lean (re-written) | Step 2 stopping/Gronwall argument is d>=3-specific (DECISIONS §7) | eq:def2_stopping@3_5:533, Gronwall_inequality@3_5:493, eq:Gronwall_dervJuD@3_5:529, defCALJ@3_5:365, lem:newKLK@3_5:371, lem:LWterm@3_5:385, lem: EMn2_N@3_5:427, Eq:Gdecay_w@1_2:1349; GavLGEX@3_5:33; GiiGEX@3_5:21; GijGEX@3_5:24; Gtmwc@1_2:1327; con_st_ind@1_2:1296; lRB1@1_2:1321; lem_GbEXP@3_5:14 |
| KellStar.lean | 406 | 355 | b | RBM3D/Path/KellStar.lean | exponent tokens 34 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| Kernel.lean | 355 | 264 | b | RBM3D/Path/Kernel.lean | exponent tokens 1 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | def_Ustz@3_5:116; int_K-L_ST@3_5:136 |
| LemDecCalE.lean | 1258 | 857 | b | RBM3D/Path/LemDecCalE.lean | exponent tokens 110 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | GijGEX@3_5:24; def_ELKLK@3_5:97; def_WTuD@3_5:2297; lem_dec_calE@3_5:2317; res_deccalE_lk@3_5:2318 |
| LemDecCalEdif.lean | 1691 | 1664 | b | RBM3D/Path/LemDecCalEdif.lean | exponent tokens 81 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | defEOTE@3_5:176; lRB1@1_2:1321; lem_dec_calE@3_5:2317; res_deccalE_dif@3_5:2329 |
| LemDecCalEwG.lean | 1402 | 1385 | b | RBM3D/Path/LemDecCalEwG.lean | exponent tokens 80 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | lRB1@1_2:1321; lem_dec_calE@3_5:2317; res_deccalE_wG@3_5:2325; GavLGEX@3_5:33 |
| LoopStep.lean | 429 | 339 | b | RBM3D/Path/LoopStep.lean | exponent tokens 3 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| Markov.lean | 766 | 679 | a | RBM3D/Path/Markov.lean | generic grid Markov property on the walk carrier |  |
| NetLift.lean | 1784 | -1 | b | RBM3D/Path/NetLift.lean | deleted by RBM2D T2274 as dead code (not reached from RBM2D's endpoint `locSC`, whose `forall z` is outside the probability); needed if the RBM3D endpoint keeps the paper's intersection over z inside P (1_2:388-393): net lift per time -> uniform in u | Eq:Gdecay_w@1_2:1349; Gt_bound_flow@1_2:1342 |
| OneStep.lean | 1692 | 1668 | b | RBM3D/Path/OneStep.lean | exponent tokens 22 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| PerTime.lean | 237 | 168 | a | RBM3D/Path/PerTime.lean | per-time domination interface; generic in the scale | stoch_domination@1_2:229 |
| QVForm.lean | 325 | 157 | b | RBM3D/Path/QVForm.lean | exponent tokens 2 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| QVIdentity.lean | 844 | 814 | b | RBM3D/Path/QVIdentity.lean | exponent tokens 40 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | alu9_STime@3_5:229; defEOTE@3_5:176; def_diffakn_k@3_5:187 |
| Scales.lean | 344 | 263 | c | RBM3D/Path/Scales.lean (re-written) | M_u = W^2 l_u^2 eta_u and l_u = min((1-u)^(-1/2),L) are d=2 scales; control is W^{-d}B_{t,0} | eq:ellt@1_2:1121, eq_B_param@1_2:1107, con_st_ind@1_2:1296 (merged Defs/Params.lean: ellT, Bparam); con_st_ind@1_2:1296; eq:bcal_k@1_2:1056; eta@1_2:720; def_WTuD@3_5:2297 |
| ScalesBridge.lean | 72 | 56 | d | none: RBM3D has the single merged ellT/etaT | superseded by merged RBM3D |  |
| Step2Close.lean | 325 | 133 | c | RBM3D/Path/Step2Close.lean (re-written) | Step 2 stopping/Gronwall argument is d>=3-specific (DECISIONS §7) | eq:def2_stopping@3_5:533, Gronwall_inequality@3_5:493, eq:Gronwall_dervJuD@3_5:529, defCALJ@3_5:365, lem:newKLK@3_5:371, lem:LWterm@3_5:385, lem: EMn2_N@3_5:427, Eq:Gdecay_w@1_2:1349; Eq:Gdecay_w@1_2:1349; Gt_bound_flow@1_2:1342; lem:main_ind@1_2:1256; lem_GbEXP@3_5:14 |
| Step2Grid.lean | 984 | 836 | c | RBM3D/Path/Step2Grid.lean (re-written) | Step 2 stopping/Gronwall argument is d>=3-specific (DECISIONS §7) | eq:def2_stopping@3_5:533, Gronwall_inequality@3_5:493, eq:Gronwall_dervJuD@3_5:529, defCALJ@3_5:365, lem:newKLK@3_5:371, lem:LWterm@3_5:385, lem: EMn2_N@3_5:427, Eq:Gdecay_w@1_2:1349; lem:main_ind@1_2:1256; con_st_ind@1_2:1296; example@A:548 |
| Step2Local.lean | 557 | 428 | c | RBM3D/Path/Step2Local.lean (re-written) | Step 2 stopping/Gronwall argument is d>=3-specific (DECISIONS §7) | eq:def2_stopping@3_5:533, Gronwall_inequality@3_5:493, eq:Gronwall_dervJuD@3_5:529, defCALJ@3_5:365, lem:newKLK@3_5:371, lem:LWterm@3_5:385, lem: EMn2_N@3_5:427, Eq:Gdecay_w@1_2:1349; Eq:Gdecay_w@1_2:1349; GiiGEX@3_5:21; GijGEX@3_5:24; Gt_bound_flow@1_2:1342; lem_GbEXP@3_5:14; Gtmwc@1_2:1327; con_st_ind@1_2:1296 |
| Step2Props.lean | 333 | 238 | b | RBM3D/Path/Step2Props.lean | exponent tokens 3 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Eq:Gdecay+IND@1_2:1267; Eq:Gdecay_w@1_2:1349; Gt_bound+IND@1_2:1276; Gt_bound_flow@1_2:1342; Gtmwc@1_2:1327; Kn2sol@1_2:1175; Main_DEL_COND@1_2:359; con_st_ind@1_2:1296 |
| Step2PropsV3.lean | 110 | 47 | c | RBM3D/Path/Step2PropsV3.lean (re-written) | Step 2 stopping/Gronwall argument is d>=3-specific (DECISIONS §7) | eq:def2_stopping@3_5:533, Gronwall_inequality@3_5:493, eq:Gronwall_dervJuD@3_5:529, defCALJ@3_5:365, lem:newKLK@3_5:371, lem:LWterm@3_5:385, lem: EMn2_N@3_5:427, Eq:Gdecay_w@1_2:1349 |
| Step2Vocab.lean | 141 | 116 | c | RBM3D/Path/Step2Vocab.lean (re-written) | Step 2 stopping/Gronwall argument is d>=3-specific (DECISIONS §7) | eq:def2_stopping@3_5:533, Gronwall_inequality@3_5:493, eq:Gronwall_dervJuD@3_5:529, defCALJ@3_5:365, lem:newKLK@3_5:371, lem:LWterm@3_5:385, lem: EMn2_N@3_5:427, Eq:Gdecay_w@1_2:1349; Eq:defGLoop@1_2:823; GijGEX@3_5:24; defEOTE@3_5:176; def_ELKLK@3_5:97; def_EwtG@1_2:961; eq:mainStoflow@1_2:951; def_diffakn_k@3_5:187 |
| StepArith.lean | 155 | 120 | c | RBM3D/Path/StepArith.lean (re-written) | Step 2 stopping/Gronwall argument is d>=3-specific (DECISIONS §7) | eq:def2_stopping@3_5:533, Gronwall_inequality@3_5:493, eq:Gronwall_dervJuD@3_5:529, defCALJ@3_5:365, lem:newKLK@3_5:371, lem:LWterm@3_5:385, lem: EMn2_N@3_5:427, Eq:Gdecay_w@1_2:1349 |
| StepBound.lean | 1653 | 1618 | c | RBM3D/Path/StepBound.lean (re-written) | Step 2 stopping/Gronwall argument is d>=3-specific (DECISIONS §7) | eq:def2_stopping@3_5:533, Gronwall_inequality@3_5:493, eq:Gronwall_dervJuD@3_5:529, defCALJ@3_5:365, lem:newKLK@3_5:371, lem:LWterm@3_5:385, lem: EMn2_N@3_5:427, Eq:Gdecay_w@1_2:1349 |
| StepDecomp.lean | 1553 | 1321 | b | RBM3D/Path/StepDecomp.lean | exponent tokens 18 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| StepDecompLoop.lean | 783 | 637 | b | RBM3D/Path/StepDecompLoop.lean | exponent tokens 22 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) |  |
| Stop.lean | 256 | 200 | a | RBM3D/Path/Stop.lean | generic grid stopping times |  |
| TailSums.lean | 799 | 738 | d | RBM3D/Defs/RadialSum.lean, Defs/Convolution.lean, Kernel/PropT.lean (lem:propT, d>=3 tail sums) | superseded by merged RBM3D | res_deccalE_wG@3_5:2325 |
| TimeSums.lean | 691 | 402 | c | RBM3D/Path/TimeSums.lean (re-written) | Step 2 stopping/Gronwall argument is d>=3-specific (DECISIONS §7) | eq:def2_stopping@3_5:533, Gronwall_inequality@3_5:493, eq:Gronwall_dervJuD@3_5:529, defCALJ@3_5:365, lem:newKLK@3_5:371, lem:LWterm@3_5:385, lem: EMn2_N@3_5:427, Eq:Gdecay_w@1_2:1349 |
| Transfer.lean | 212 | 130 | a | RBM3D/Path/Transfer.lean | per-time transfer between grid walk and single-time model |  |
| UBounds.lean | 731 | 657 | b | RBM3D/Path/UBounds.lean | exponent tokens 4 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | def_Ustz@3_5:116; lem:sum_Ndecay@3_5:1620; DefTHUST@3_5:109 |
| UTransport.lean | 665 | 542 | b | RBM3D/Path/UTransport.lean | exponent tokens 31 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | TailtoTail@3_5:2345; neiwuj@3_5:2357 |
| Walk.lean | 608 | 578 | a | RBM3D/Path/Walk.lean | grid walk carrier over Sizes.SeqOmega: depends on d only through Sizes |  |

### Universality -> RBM3D/Universality

| RBM2D file | lines c9a24cf | kept 0c1330a | class | RBM3D target | basis | labels (this paper) |
|---|---|---|---|---|---|---|
| Apriori.lean | 424 | 378 | b | RBM3D/Universality/Apriori.lean | exponent tokens 13 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | G_bound@1_2:388 |
| EMCTE2.lean | 726 | 631 | b | RBM3D/Universality/EMCTE2.lean | exponent tokens 3 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Thm: B_Univ@1_2:452 (dir default) |
| EigenInterlacing.lean | 623 | 592 | a | RBM3D/Universality/EigenInterlacing.lean | no exponent token; renaming R1-R4 only (lattice tokens 0, Sizes tokens 0) | Thm: B_Univ@1_2:452 (dir default) |
| EigenMeasurable.lean | 582 | 479 | a | RBM3D/Universality/EigenMeasurable.lean | no exponent token; renaming R1-R4 only (lattice tokens 3, Sizes tokens 0) | Thm: B_Univ@1_2:452 (dir default) |
| FreeConv.lean | 719 | 667 | a | RBM3D/Universality/FreeConv.lean | no exponent token; renaming R1-R4 only (lattice tokens 0, Sizes tokens 1) | Thm: B_Univ@1_2:452 (dir default) |
| FreeConvStability.lean | 835 | 788 | b | RBM3D/Universality/FreeConvStability.lean | exponent tokens 1 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Thm: B_Univ@1_2:452 (dir default) |
| GUEInvariance.lean | 1082 | 1004 | b | RBM3D/Universality/GUEInvariance.lean | exponent tokens 4 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Thm: B_Univ@1_2:452 (dir default) |
| GUELocalBootstrap.lean | 1042 | 995 | b | RBM3D/Universality/GUELocalBootstrap.lean | exponent tokens 5 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | MR:locSC@1_2:386 |
| GUELocalSchur.lean | 673 | 578 | b | RBM3D/Universality/GUELocalSchur.lean | exponent tokens 19 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | MR:locSC@1_2:386 |
| GUEPhase/AuxCarrier.lean | 1183 | 1082 | b | RBM3D/Universality/GUEPhase/AuxCarrier.lean | exponent tokens 13 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Thm: B_Univ@1_2:452 (dir default) |
| GUEPhase/Bootstrap.lean | 1465 | 595 | b | RBM3D/Universality/GUEPhase/Bootstrap.lean | exponent tokens 52 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | example@A:548 |
| GUEPhase/BootstrapAt.lean | 855 | 754 | b | RBM3D/Universality/GUEPhase/BootstrapAt.lean | exponent tokens 2 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Thm: B_Univ@1_2:452 (dir default) |
| GUEPhase/BoundsA.lean | 884 | 746 | b | RBM3D/Universality/GUEPhase/BoundsA.lean | exponent tokens 17 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Thm: B_Univ@1_2:452 (dir default) |
| GUEPhase/Drift.lean | 2184 | 2093 | b | RBM3D/Universality/GUEPhase/Drift.lean | exponent tokens 29 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Thm: B_Univ@1_2:452 (dir default) |
| GUEPhase/DuhamelA.lean | 2355 | 2052 | b | RBM3D/Universality/GUEPhase/DuhamelA.lean | exponent tokens 25 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Thm: B_Univ@1_2:452 (dir default) |
| GUEPhase/DuhamelB.lean | 1344 | 1064 | b | RBM3D/Universality/GUEPhase/DuhamelB.lean | exponent tokens 4 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Thm: B_Univ@1_2:452 (dir default) |
| GUEPhase/DuhamelC.lean | 1645 | 1543 | b | RBM3D/Universality/GUEPhase/DuhamelC.lean | exponent tokens 11 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Thm: B_Univ@1_2:452 (dir default) |
| GUEPhase/EntryDet.lean | 1362 | 837 | b | RBM3D/Universality/GUEPhase/EntryDet.lean | exponent tokens 69 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Thm: B_Univ@1_2:452 (dir default) |
| GUEPhase/EntryGrid.lean | 1042 | 925 | b | RBM3D/Universality/GUEPhase/EntryGrid.lean | exponent tokens 7 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Thm: B_Univ@1_2:452 (dir default) |
| GUEPhase/EntryTail.lean | 1675 | 1519 | b | RBM3D/Universality/GUEPhase/EntryTail.lean | exponent tokens 18 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | lem_GbEXP@3_5:14 |
| GUEPhase/Eq729A.lean | 1430 | 1087 | b | RBM3D/Universality/GUEPhase/Eq729A.lean | exponent tokens 68 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Thm: B_Univ@1_2:452 (dir default) |
| GUEPhase/Eq729B.lean | 1631 | 1442 | b | RBM3D/Universality/GUEPhase/Eq729B.lean | exponent tokens 6 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | eq:zztE@1_2:791 |
| GUEPhase/Generator.lean | 1199 | 1152 | b | RBM3D/Universality/GUEPhase/Generator.lean | exponent tokens 44 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Thm: B_Univ@1_2:452 (dir default) |
| GUEPhase/Grid.lean | 888 | 768 | b | RBM3D/Universality/GUEPhase/Grid.lean | exponent tokens 7 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | eq:zztE@1_2:791 |
| GUEPhase/HypA.lean | 1521 | 1032 | b | RBM3D/Universality/GUEPhase/HypA.lean | exponent tokens 37 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Thm: B_Univ@1_2:452 (dir default) |
| GUEPhase/HypB.lean | 1814 | 1063 | b | RBM3D/Universality/GUEPhase/HypB.lean | exponent tokens 30 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Thm: B_Univ@1_2:452 (dir default) |
| GUEPhase/KPrim.lean | 909 | 799 | b | RBM3D/Universality/GUEPhase/KPrim.lean | exponent tokens 66 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Kn2sol@1_2:1175; example@A:548; pro_dyncalK@1_2:990 |
| GUEPhase/LLTransfer.lean | 670 | 467 | b | RBM3D/Universality/GUEPhase/LLTransfer.lean | exponent tokens 5 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | eq:zztE@1_2:791 |
| GUEPhase/Markov.lean | 1085 | 923 | b | RBM3D/Universality/GUEPhase/Markov.lean | exponent tokens 3 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Thm: B_Univ@1_2:452 (dir default) |
| GUEPhase/OneLoop.lean | 1848 | 1750 | b | RBM3D/Universality/GUEPhase/OneLoop.lean | exponent tokens 71 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Thm: B_Univ@1_2:452 (dir default) |
| GUEPhase/PathBounds.lean | 680 | 566 | b | RBM3D/Universality/GUEPhase/PathBounds.lean | exponent tokens 17 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Thm: B_Univ@1_2:452 (dir default) |
| GUEPhase/Proc.lean | 1768 | 1440 | b | RBM3D/Universality/GUEPhase/Proc.lean | exponent tokens 71 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Thm: B_Univ@1_2:452 (dir default) |
| GUEPhase/RandomLayerA.lean | 820 | 549 | b | RBM3D/Universality/GUEPhase/RandomLayerA.lean | exponent tokens 22 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | eq:zztE@1_2:791 |
| GUEPhase/RandomLayerB.lean | 278 | 180 | b | RBM3D/Universality/GUEPhase/RandomLayerB.lean | exponent tokens 3 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | example@A:548 |
| GUETranslation.lean | 1303 | 1171 | a | RBM3D/Universality/GUETranslation.lean | no exponent token; renaming R1-R4 only (lattice tokens 22, Sizes tokens 323) | MR:locSC@1_2:386 |
| GreenCorr.lean | 810 | 740 | a | RBM3D/Universality/GreenCorr.lean | no exponent token; renaming R1-R4 only (lattice tokens 29, Sizes tokens 54) | Thm: B_Univ@1_2:452 (dir default) |
| InjSum.lean | 601 | 537 | a | RBM3D/Universality/InjSum.lean | no exponent token; renaming R1-R4 only (lattice tokens 0, Sizes tokens 0) | Thm: B_Univ@1_2:452 (dir default) |
| Jak.lean | 952 | 923 | b | RBM3D/Universality/Jak.lean | exponent tokens 10 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Thm: B_Univ@1_2:452 |
| JakKernel.lean | 1121 | 970 | b | RBM3D/Universality/JakKernel.lean | exponent tokens 53 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Thm: B_Univ@1_2:452 (dir default) |
| JakSpectral.lean | 720 | 597 | b | RBM3D/Universality/JakSpectral.lean | exponent tokens 52 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Meq:QUE@1_2:411 |
| OU.lean | 299 | 197 | b | RBM3D/Universality/OU.lean | exponent tokens 1 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Thm: B_Univ@1_2:452 (dir default) |
| OUContraction.lean | 1109 | 1055 | a | RBM3D/Universality/OUContraction.lean | no exponent token; renaming R1-R4 only (lattice tokens 233, Sizes tokens 1) | Thm: B_Univ@1_2:452 (dir default) |
| OUGenerator.lean | 1223 | 1185 | b | RBM3D/Universality/OUGenerator.lean | exponent tokens 7 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Thm: B_Univ@1_2:452 (dir default) |
| OUHessian.lean | 1242 | 1102 | b | RBM3D/Universality/OUHessian.lean | exponent tokens 4 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Thm: B_Univ@1_2:452 (dir default) |
| Pins.lean | 683 | 550 | b | RBM3D/Universality/Pins.lean | exponent tokens 9 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Thm: B_Univ@1_2:452; G_bound@1_2:388; G_bound_ave@1_2:391; ML:GLoop@1_2:1193; ML:GLoop_expec@1_2:1203; ML:GtLocal@1_2:1217; MR:locSC@1_2:386; Meq:QUE@1_2:411 |
| PoissonSmoothing.lean | 1077 | 1034 | a | RBM3D/Universality/PoissonSmoothing.lean | no exponent token; renaming R1-R4 only (lattice tokens 0, Sizes tokens 0) | Thm: B_Univ@1_2:452 (dir default) |
| QUEFlow.lean | 961 | 925 | b | RBM3D/Universality/QUEFlow.lean | exponent tokens 54 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Meq:QUE@1_2:411 |
| Step1Band.lean | 1259 | 1163 | b | RBM3D/Universality/Step1Band.lean | exponent tokens 3 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Thm: B_Univ@1_2:452 (dir default) |
| Step1Cond.lean | 947 | 798 | a | RBM3D/Universality/Step1Cond.lean | no exponent token; renaming R1-R4 only (lattice tokens 36, Sizes tokens 2) | Thm: B_Univ@1_2:452 (dir default) |
| Step1RegularityA.lean | 978 | 927 | b | RBM3D/Universality/Step1RegularityA.lean | exponent tokens 59 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | G_bound_ave@1_2:391 |
| Step1RegularityB.lean | 906 | 839 | b | RBM3D/Universality/Step1RegularityB.lean | exponent tokens 36 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Thm: B_Univ@1_2:452 |
| Step1RegularityGUE.lean | 1221 | 1051 | b | RBM3D/Universality/Step1RegularityGUE.lean | exponent tokens 33 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | MR:locSC@1_2:386 |
| UnivMain.lean | 552 | 474 | b | RBM3D/Universality/UnivMain.lean | exponent tokens 12 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Thm: B_Univ@1_2:452 |
| Uyw.lean | 1021 | 972 | b | RBM3D/Universality/Uyw.lean | exponent tokens 15 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Thm: B_Univ@1_2:452 |
| UywKernel.lean | 1372 | 1170 | b | RBM3D/Universality/UywKernel.lean | exponent tokens 64 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Meq:QUE@1_2:411 |
| ZeroModeProfile.lean | 1269 | 566 | b | RBM3D/Universality/ZeroModeProfile.lean | exponent tokens 57 (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g) | Thm: B_Univ@1_2:452 (dir default) |

## D. Directory-level rows

| RBM2D dir (directory level only) | covered by | files | lines c9a24cf | lines kept 0c1330a | files reachable from the endpoints | lines reachable |
|---|---|---|---|---|---|---|
| Analysis | none needed: no file is reachable from the endpoints | 4 | 513 | 0 | 0 | 0 |
| (root files) | RBM3D/{Basic,Delocalization,Endpoints}.lean (T2001 freeze) | 3 | 459 | 415 | 2 | 422 |
| Loop | RBM3D/Loop (T2004: K-loops, KBound, SumZero, Ward, TreeRep, PureLoop) | 16 | 16475 | 15073 | 16 | 16475 |
| Propagator | RBM3D/Propagator + RBM3D/Kernel (T2003: Theta decay, Combes-Thomas, cutoff, symbol) | 87 | 17266 | 9553 | 56 | 11814 |
| Test | RBM3D/Test (axiom audit; not ported) | 2 | 293 | 51 | 0 | 0 |

## E. Summaries

| RBM2D dir -> RBM3D dir | files | lines c9a24cf | lines kept 0c1330a | files a/b/c/d | lines a/b/c/d |
|---|---|---|---|---|---|
| Defs -> RBM3D/Defs | 7 | 2028 | 1361 | 1/1/0/5 | 611/285/0/1132 |
| Gauss -> RBM3D/Gauss | 47 | 7427 | 4669 | 19/13/0/15 | 3549/2410/0/1468 |
| Green -> RBM3D/Green | 34 | 26927 | 20318 | 9/24/1/0 | 5847/20665/415/0 |
| Hierarchy -> RBM3D/Hierarchy | 47 | 5718 | 2639 | 8/17/0/22 | 774/2457/0/2487 |
| Path -> RBM3D/Path | 42 | 31716 | 25041 | 6/19/15/2 | 2418/17704/10723/871 |
| Induction -> RBM3D/Induction | 60 | 69835 | 53876 | 2/55/2/1 | 1510/67729/492/104 |
| Evolution -> RBM3D/Evolution | 24 | 24625 | 21947 | 0/17/7/0 | 0/16772/7853/0 |
| Main -> RBM3D/Main | 9 | 4066 | 2847 | 2/7/0/0 | 147/3919/0/0 |
| Universality -> RBM3D/Universality | 56 | 60867 | 51486 | 9/47/0/0 | 7771/53096/0/0 |
| TOTAL | 326 | 233209 | 184184 | 56/200/25/45 | 22627/185037/19483/6062 |

| sub-gate (proposal, dependency order) | files | lines c9a24cf | lines kept 0c1330a | files a/b/c/d |
|---|---|---|---|---|
| MD vocabulary (split table, section MD) | 18 | 6580 | 4568 | 14/4/0/0 |
| ST-1 Gaussian calculus, loop algebra, Step 1 (lem_GbEXP, lem_ConArg) | 86 | 38498 | 29932 | 29/56/1/0 |
| ST-2 path layer and Step 2 (grid, stopping, one-step expansion, d>=3 argument) | 46 | 41618 | 31831 | 0/30/16/0 |
| ST-3 Steps 3-4 (alternating/non-alternating, Q-process, (+,+) base) | 40 | 50203 | 38991 | 2/37/1/0 |
| ST-4 Step 5 (CLT, lem:sum_decay, lem_dec_calE inputs) | 17 | 16772 | 15101 | 0/17/0/0 |
| ST-5 Step 6 (expected 2-loop, ML:exp) | 7 | 7853 | 6846 | 0/0/7/0 |
| ST-6 assembly (lem:main_ind chain, ML:*, endpoints MR:*) | 9 | 4609 | 3233 | 0/9/0/0 |
| UN bulk universality (Thm: B_Univ) | 58 | 61014 | 51594 | 11/47/0/0 |
| none (class d: merged or unreachable) | 45 | 6062 | 2088 | 0/0/0/45 |
| TOTAL | 326 | 233209 | 184184 | |

## E.2 Split table of the MD vocabulary tickets (computed from the rows above and the probe sections)

| ticket | files under RBM3D/ | statements | RBM2D sources | lines c9a24cf | lines kept 0c1330a | probe lines | est. lines | depends on | role |
|---|---|---|---|---|---|---|---|---|---|
| MD-1 | RBM3D/Defs/Sizes.lean, RBM3D/Gauss/FineModel.lean | Idx, blk, split(Equiv), Iblk, card_Iblk, card_Idx, zdistInf, Sizes (lam), size, WO, Bandwidth, Admissible, locDomain, withLam, W<->N conversions; svarF (svarF_eq_svar), gvarF, PF, Xentry, Xmat, Xlinear, coordinateMatrix, Hflow, seqP, slice, seqXmat, seqHflow, seqP_map_slice, E abs(X)^2 = S | Defs/Model, Gauss/Model, Gauss/LinearForm | 1141 | 910 | 407 | 1317 | none | prover-max (interface, every ST/UN ticket consumes it) |
| MD-2 | RBM3D/Defs/StochDomAt.lean, RBM3D/Gauss/DominationAt.lean | badSetAt, StochDomAt (+ calculus: refl, trans, add, mul, of_forall_le, of_unifDetDom; stochDom_iff_at_id), HighProbAt (+ inter, biInter; highProb_iff_at_id), PerTimeDomAt (+ grid union bound), Prec, PrecPT, Whp (+ prec_of_le, precPT_of_le); moment => domination and back, envelope, countable-product Stein | Defs/StochDom, Path/PerTime, Gauss/Domination, Gauss/MomentBridge, Gauss/Envelope, Gauss/SteinMatrix | 2409 | 1108 | 142 | 1250 | MD-1 | prover-hard |
| MD-3 | RBM3D/Loop/GLoopFlow.lean, RBM3D/Gauss/BlockAnderson.lean | Gres, Mres, loopM, blockMat, loopFine, loopOf/loopL, Gt, Gn, Lloop, cutGlue (+ gloop_cutGlueL_split, gloop_cutGlueR_split), envelope (5.2) for arbitrary Hermitian H, zztE (Gt_lemT), PsiI, seqHflowBA, seqHBA, Gt_BA (m(z) = integral is T2005, merged) | Hierarchy/Loops, Hierarchy/Operations, Hierarchy/OperationsPairWord, Path/Step2Props | 849 | 728 | 347 | 1075 | MD-1 | prover-max (interface: loops and flow data) |
| MD-4 | RBM3D/Path/Walk.lean | PathOmega, pathP, filt, gridStep, gridTime, pathH (+ pathH_isHermitian), PrecGrid (+ precGrid_of_le); proofs of TransferLaw, IndepIncr; per-time transfer grid <-> single time | Path/Walk, Path/Transfer | 820 | 708 | 100 | 808 | MD-1, MD-2 | prover-hard |
| MD-5 | RBM3D/Path/Markov.lean, RBM3D/Path/Stop.lean, RBM3D/Path/Azuma.lean | grid Markov property and freezing, grid stopping times, Azuma-Hoeffding + Doob (replace BDG, DECISIONS §7) | Path/Markov, Path/Stop, Path/Azuma | 1361 | 1114 | 0 | 1114 | MD-4 | prover (generic, class a) |
| total | | | | 6580 | 4568 | | | | |

## E.3 New work with no RBM2D counterpart (paper labels of this paper, checked against `texlabels.tsv`; a label not found is printed as `?`)

* Step 2 of d>=3 (no RBM2D source for the argument; DECISIONS §7): eq:def2_stopping@3_5:533, Gronwall_inequality@3_5:493, eq:Gronwall_dervJuD@3_5:529, defCALJ@3_5:365, awi2iks@3_5:346, lem:newKLK@3_5:371, lem: EMn2_N@3_5:427, ygdhmsgq0@3_5:751
* light-weight term and graph expansions (sec. 7, App. B; no sister project has them, DECISIONS §2 item 3): lem:LWterm@3_5:385, lem: EWGn2_N@3_5:406, lem:LWterm_EXP@6:83, lem:LW_moment@7_8:72, lem:LW_moment_exp@7_8:78, lem:Anp@7_8:933, lem:Anp_key@7_8:960, claim:TTk@7_8:1661, def scaling order@7_8:270, Owx@7_8:298, Oe2x@7_8:339
* Steps 3-5 regimes that d=2 does not have (1-s <= g^2/L^2 and g^2/L^d <= 1-t <= g^2/L^2): sec:1-s<L-2@3_5:1435, def;zero_mode_remove@3_5:1444, lem: newPQ@3_5:1482, lem:STOeq_Qt_nonzero@3_5:1561, lem:sum_decay_nonzero@3_5:1666, lem;CLT@3_5:2173
* block Anderson: deterministic layer and the changes of Steps 1-2 (sec. 8): zztE_BA@7_8:1796, lem:main_ind_BA@7_8:1825, lem:propM@7_8:1847, lem_GbEXP_BA@7_8:1916, lem_ConArg_BA@7_8:1956, self_m@1_2:626, def_G0@1_2:631
* propagator in d dimensions (T2003): lem_propTH@1_2:1119, def_Theta@1_2:1068, prop:ThfadC@1_2:1144, prop:BD1@1_2:1153

## F. `#print axioms` of every declaration printed by the probe (verbatim output of `lake env lean RBM3D/Probe/T2002Vocab.lean`; command and exit code: prove report b.1)

```
'RBM.Gauss.split_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.card_Iblk' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.card_Idx' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.card_Idx' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.zdistInf_le_zdistD' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.zdistD_le_mul_zdistInf' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lam_sq_mul_pow_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.W_rpow_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.size_rpow_le_W_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.svarF_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.svarF_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.svarF_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.svarF_eq_svar' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Xmat_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.seqP_map_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.seqHflow_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.PsiI_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.seqHBA_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.loopM_eq_loopL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Mres_zero_msc' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.Gt_lemT' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.Gt_BA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.Lloop_zero_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.prec_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.Prec.whp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.precPT_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.precGrid_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.stochDom_iff_at_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.highProb_iff_at_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.pathH_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2002Inst.sz0_admissible' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2002Inst.sz0_lam_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2002Inst.scales_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2002Inst.sz0_lam_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2002Inst.z0_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2002Inst.z0_zztE' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2002Inst.z0_Gt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2002Inst.svarF_sz0_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2002Inst.card_Iblk_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2002Inst.card_Idx_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2002Inst.zdistInf_inst' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2002Inst.seqP_sz0_prob' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2002Inst.seqP_sz0_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2002Inst.seqXmat_sz0_herm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2002Inst.Gt_prec' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2002Inst.Gt_whp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2002Inst.localLaw_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2002Inst.gridRes_prec' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2002Inst.Gt_timeIcc_prec' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2002Inst.loopL_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2002Inst.Mres_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2002Inst.loop_envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2002Inst.Lloop_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2002Inst.transfer_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2002Inst.indep_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2002Inst.pathP_sz0_prob' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2002Inst.gridTime_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2002Inst.Gt_BA_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2002Inst.W_le_size_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.T2002Inst.size_le_W_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## G. The pins of the probe (script `Pins.lean`, elaborated types, output verbatim; the probe is `RBM3D/Probe/T2002Vocab.lean` on branch `t/T2002`)

```
T2002Vocab.lean:47 def RBM.Gauss.Idx : ℕ → ℕ → ℕ → Type
T2002Vocab.lean:51 def RBM.Gauss.blk : (L W : ℕ) → ZMod (W * L) → ZMod L
T2002Vocab.lean:57 def RBM.Gauss.ofs : (L W : ℕ) → [NeZero W] → ZMod (W * L) → Fin W
T2002Vocab.lean:64 def RBM.Gauss.split : (d L W : ℕ) → [NeZero W] → RBM.Gauss.Idx d L W → RBM.Gauss.Vtx d L W
T2002Vocab.lean:87 def RBM.Gauss.splitEquiv : (d L W : ℕ) → [NeZero L] → [NeZero W] → RBM.Gauss.Idx d L W ≃ RBM.Gauss.Vtx d L W
T2002Vocab.lean:93 def RBM.Gauss.Iblk : (d L W : ℕ) → [NeZero L] → [NeZero W] → RBM.Zd d L → Finset (RBM.Gauss.Idx d L W)
T2002Vocab.lean:115 def RBM.Gauss.zdistInf : (d L : ℕ) → RBM.Zd d L → ℕ
T2002Vocab.lean:133 structure RBM.Gauss.Sizes : ℕ → Type
T2002Vocab.lean:158 def RBM.Gauss.Sizes.size : {d : ℕ} → RBM.Gauss.Sizes d → ℕ → ℕ
T2002Vocab.lean:166 def RBM.Gauss.Sizes.WO : {d : ℕ} → RBM.Gauss.Sizes d → ℝ → Prop
T2002Vocab.lean:170 def RBM.Gauss.Sizes.Bandwidth : {d : ℕ} → RBM.Gauss.Sizes d → ℝ → Prop
T2002Vocab.lean:174 def RBM.Gauss.Sizes.SizeTendsto : {d : ℕ} → RBM.Gauss.Sizes d → Prop
T2002Vocab.lean:178 def RBM.Gauss.Sizes.Admissible : {d : ℕ} → RBM.Gauss.Sizes d → ℝ → ℝ → Prop
T2002Vocab.lean:183 def RBM.Gauss.Sizes.withLam : {d : ℕ} → RBM.Gauss.Sizes d → (ℕ → ℝ) → RBM.Gauss.Sizes d
T2002Vocab.lean:187 def RBM.Gauss.Sizes.locDomain : {d : ℕ} → RBM.Gauss.Sizes d → ℝ → ℝ → ℕ → ℂ → Prop
T2002Vocab.lean:213 def RBM.Gauss.Sizes.Bctl : {d : ℕ} → RBM.Gauss.Sizes d → ℕ → ℝ → ℝ
T2002Vocab.lean:257 def RBM.Gauss.svarF : (d L W : ℕ) → ℝ → [NeZero W] → RBM.Gauss.Idx d L W → RBM.Gauss.Idx d L W → ℝ
T2002Vocab.lean:285 def RBM.Gauss.idxKey : (d L W : ℕ) → [NeZero L] → [NeZero W] → RBM.Gauss.Idx d L W → ℕ
T2002Vocab.lean:292 def RBM.Gauss.CoordF : ℕ → ℕ → ℕ → Type
T2002Vocab.lean:296 def RBM.Gauss.Ω : ℕ → ℕ → ℕ → Type
T2002Vocab.lean:300 def RBM.Gauss.gvarF : (d L W : ℕ) → ℝ → [NeZero W] → RBM.Gauss.CoordF d L W → NNReal
T2002Vocab.lean:309 def RBM.Gauss.PF : (d L W : ℕ) → ℝ → [NeZero W] → MeasureTheory.Measure (RBM.Gauss.Ω d L W)
T2002Vocab.lean:317 def RBM.Gauss.Xentry : (d L W : ℕ) → [NeZero L] → [NeZero W] → RBM.Gauss.Ω d L W → RBM.Gauss.Idx d L W → RBM.Gauss.Idx d L W → ℂ
T2002Vocab.lean:326 def RBM.Gauss.Xmat : (d L W : ℕ) → [NeZero L] → [NeZero W] → RBM.Gauss.Ω d L W → Matrix (RBM.Gauss.Idx d L W) (RBM.Gauss.Idx d L W) ℂ
T2002Vocab.lean:368 def RBM.Gauss.Sizes.SeqCoord : {d : ℕ} → RBM.Gauss.Sizes d → Type
T2002Vocab.lean:372 def RBM.Gauss.Sizes.SeqΩ : {d : ℕ} → RBM.Gauss.Sizes d → Type
T2002Vocab.lean:376 def RBM.Gauss.Sizes.seqGvar : {d : ℕ} → (sz : RBM.Gauss.Sizes d) → sz.SeqCoord → NNReal
T2002Vocab.lean:380 def RBM.Gauss.Sizes.seqP : {d : ℕ} → (sz : RBM.Gauss.Sizes d) → MeasureTheory.Measure sz.SeqΩ
T2002Vocab.lean:388 def RBM.Gauss.Sizes.slice : {d : ℕ} → (sz : RBM.Gauss.Sizes d) → (n : ℕ) → sz.SeqΩ → RBM.Gauss.Ω d (sz.L n) (sz.W n)
T2002Vocab.lean:430 def RBM.Gauss.Sizes.seqXmat : {d : ℕ} →  (sz : RBM.Gauss.Sizes d) →   (n : ℕ) → sz.SeqΩ → Matrix (RBM.Gauss.Idx d (sz.L n) (sz.W n)) (RBM.Gauss.Idx d (sz.L n) (sz.W n)) ℂ
T2002Vocab.lean:435 def RBM.Gauss.Sizes.seqHflow : {d : ℕ} →  (sz : RBM.Gauss.Sizes d) →   (n : ℕ) → ℝ → sz.SeqΩ → Matrix (RBM.Gauss.Idx d (sz.L n) (sz.W n)) (RBM.Gauss.Idx d (sz.L n) (sz.W n)) ℂ
T2002Vocab.lean:456 def RBM.Gauss.PsiB : (d L : ℕ) → Matrix (RBM.Zd d L) (RBM.Zd d L) ℂ
T2002Vocab.lean:460 def RBM.Gauss.PsiV : (d L W : ℕ) → Matrix (RBM.Gauss.Vtx d L W) (RBM.Gauss.Vtx d L W) ℂ
T2002Vocab.lean:464 def RBM.Gauss.PsiI : (d L W : ℕ) → [NeZero L] → [NeZero W] → Matrix (RBM.Gauss.Idx d L W) (RBM.Gauss.Idx d L W) ℂ
T2002Vocab.lean:490 def RBM.Gauss.Sizes.seqHflowBA : {d : ℕ} →  (sz : RBM.Gauss.Sizes d) →   (ℕ → ℝ) → (n : ℕ) → ℝ → sz.SeqΩ → Matrix (RBM.Gauss.Idx d (sz.L n) (sz.W n)) (RBM.Gauss.Idx d (sz.L n) (sz.W n)) ℂ
T2002Vocab.lean:507 def RBM.Gauss.ztOf : ℂ → ℝ → ℝ → ℂ
T2002Vocab.lean:512 def RBM.Gauss.etaOf : ℂ → ℝ → ℝ
T2002Vocab.lean:524 def RBM.Gauss.Gres : {ι : Type u_1} → [Fintype ι] → [DecidableEq ι] → Matrix ι ι ℂ → ℂ → Bool → Matrix ι ι ℂ
T2002Vocab.lean:532 def RBM.Gauss.Mres : {ι : Type u_1} → [Fintype ι] → [DecidableEq ι] → Matrix ι ι ℂ → ℂ → ℂ → Matrix ι ι ℂ
T2002Vocab.lean:544 def RBM.Gauss.loopM : (d L W : ℕ) →  [NeZero L] →   Matrix (RBM.Gauss.Vtx d L W) (RBM.Gauss.Vtx d L W) ℂ → ℂ → {n : ℕ} → (Fin n → Bool) → (Fin n → RBM.Zd d L) → ℂ
T2002Vocab.lean:557 def RBM.Gauss.blockMat : (d L W : ℕ) →  [NeZero L] →   [NeZero W] →    Matrix (RBM.Gauss.Idx d L W) (RBM.Gauss.Idx d L W) ℂ → Matrix (RBM.Gauss.Vtx d L W) (RBM.Gauss.Vtx d L W) ℂ
T2002Vocab.lean:563 def RBM.Gauss.loopFine : (d L W : ℕ) →  [NeZero L] →   [NeZero W] →    Matrix (RBM.Gauss.Idx d L W) (RBM.Gauss.Idx d L W) ℂ → ℂ → {k : ℕ} → (Fin k → Bool) → (Fin k → RBM.Zd d L) → ℂ
T2002Vocab.lean:569 def RBM.Gauss.loopOf : {α : Type u_2} → {k : ℕ} → (Fin k → Bool) → (Fin k → α) → RBM.Loop.LoopIdx α
T2002Vocab.lean:575 def RBM.Gauss.loopL : (d L W : ℕ) → [NeZero L] → Matrix (RBM.Gauss.Vtx d L W) (RBM.Gauss.Vtx d L W) ℂ → ℂ → RBM.Loop.LoopIdx (RBM.Zd d L) → ℂ
T2002Vocab.lean:604 def RBM.Gauss.Sizes.Gt : {d : ℕ} →  (sz : RBM.Gauss.Sizes d) →   (n : ℕ) → ℝ → ℝ → Bool → sz.SeqΩ → Matrix (RBM.Gauss.Idx d (sz.L n) (sz.W n)) (RBM.Gauss.Idx d (sz.L n) (sz.W n)) ℂ
T2002Vocab.lean:611 def RBM.Gauss.Sizes.Lloop : {d : ℕ} →  (sz : RBM.Gauss.Sizes d) → (n : ℕ) → ℝ → ℝ → {k : ℕ} → (Fin k → Bool) → (Fin k → RBM.Zd d (sz.L n)) → sz.SeqΩ → ℂ
T2002Vocab.lean:617 def RBM.Gauss.Sizes.Gn : {d : ℕ} →  (sz : RBM.Gauss.Sizes d) →   (n : ℕ) → ℂ → sz.SeqΩ → Matrix (RBM.Gauss.Idx d (sz.L n) (sz.W n)) (RBM.Gauss.Idx d (sz.L n) (sz.W n)) ℂ
T2002Vocab.lean:656 def RBM.Gauss.Sizes.seqHBA : {d : ℕ} →  (sz : RBM.Gauss.Sizes d) →   (n : ℕ) → sz.SeqΩ → Matrix (RBM.Gauss.Idx d (sz.L n) (sz.W n)) (RBM.Gauss.Idx d (sz.L n) (sz.W n)) ℂ
T2002Vocab.lean:803 def RBM.badSetAt : {Ω : Type u_1} → {U : ℕ → Type u_2} → (ℕ → ℕ) → ((l : ℕ) → U l → Ω → ℝ) → ((l : ℕ) → U l → Ω → ℝ) → ℝ → ℕ → Set Ω
T2002Vocab.lean:808 def RBM.StochDomAt : {Ω : Type u_1} →  [inst : MeasurableSpace Ω] →   MeasureTheory.Measure Ω → {U : ℕ → Type u_2} → (ℕ → ℕ) → ((l : ℕ) → U l → Ω → ℝ) → ((l : ℕ) → U l → Ω → ℝ) → Prop
T2002Vocab.lean:832 def RBM.Gauss.HighProbAt : {Ω : Type u_1} → [inst : MeasurableSpace Ω] → MeasureTheory.Measure Ω → (ℕ → ℕ) → (ℕ → Set Ω) → Prop
T2002Vocab.lean:851 def RBM.Path.TimeIcc : (ℕ → ℝ) → (ℕ → ℝ) → ℕ → Type
T2002Vocab.lean:854 def RBM.Path.PerTimeDomAt : {Ω : Type u_1} →  [inst : MeasurableSpace Ω] →   MeasureTheory.Measure Ω → (ℕ → ℕ) → {U : ℕ → Type u_2} → ((l : ℕ) → U l → Ω → ℝ) → ((l : ℕ) → U l → Ω → ℝ) → Prop
T2002Vocab.lean:869 def RBM.Gauss.Sizes.Prec : {d : ℕ} →  (sz : RBM.Gauss.Sizes d) → {U : ℕ → Type u_1} → ((n : ℕ) → U n → sz.SeqΩ → ℝ) → ((n : ℕ) → U n → sz.SeqΩ → ℝ) → Prop
T2002Vocab.lean:875 def RBM.Gauss.Sizes.PrecPT : {d : ℕ} →  (sz : RBM.Gauss.Sizes d) → {U : ℕ → Type u_1} → ((n : ℕ) → U n → sz.SeqΩ → ℝ) → ((n : ℕ) → U n → sz.SeqΩ → ℝ) → Prop
T2002Vocab.lean:879 def RBM.Gauss.Sizes.Whp : {d : ℕ} → (sz : RBM.Gauss.Sizes d) → (ℕ → Set sz.SeqΩ) → Prop
T2002Vocab.lean:882 def RBM.Gauss.Sizes.LocalLawPT : {d : ℕ} → RBM.Gauss.Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop
T2002Vocab.lean:945 def RBM.Path.PathΩ : {d : ℕ} → RBM.Gauss.Sizes d → Type
T2002Vocab.lean:950 def RBM.Path.pathP : {d : ℕ} → (sz : RBM.Gauss.Sizes d) → MeasureTheory.Measure (RBM.Path.PathΩ sz)
T2002Vocab.lean:954 def RBM.Path.filt : {d : ℕ} → (sz : RBM.Gauss.Sizes d) → MeasureTheory.Filtration ℕ inferInstance
T2002Vocab.lean:959 def RBM.Path.gridStep : (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℕ) → ℕ → ℝ
T2002Vocab.lean:963 def RBM.Path.gridTime : (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℕ) → ℕ → ℕ → ℝ
T2002Vocab.lean:966 def RBM.Path.pathH : {d : ℕ} →  (sz : RBM.Gauss.Sizes d) →   (ℕ → ℝ) →    (ℕ → ℝ) →     (ℕ → ℕ) →      (n : ℕ) →       ℕ → RBM.Path.PathΩ sz → Matrix (RBM.Gauss.Idx d (sz.L n) (sz.W n)) (RBM.Gauss.Idx d (sz.L n) (sz.W n)) ℂ
T2002Vocab.lean:974 def RBM.Path.TransferLaw : {d : ℕ} → RBM.Gauss.Sizes d → Prop
T2002Vocab.lean:982 def RBM.Path.IndepIncr : {d : ℕ} → RBM.Gauss.Sizes d → Prop
T2002Vocab.lean:1013 def RBM.Gauss.Sizes.PrecGrid : {d : ℕ} →  (sz : RBM.Gauss.Sizes d) →   {U : ℕ → Type u_1} → ((n : ℕ) → U n → RBM.Path.PathΩ sz → ℝ) → ((n : ℕ) → U n → RBM.Path.PathΩ sz → ℝ) → Prop
T2002Vocab.lean:1048 def RBM.Gauss.T2002Inst.sz0 : RBM.Gauss.Sizes 3
T2002Vocab.lean:1159 def RBM.Gauss.T2002Inst.z0 : ℂ
T2002Vocab.lean:1230 def RBM.Gauss.T2002Inst.Eseq : ℕ → ℝ
```

## H. The compiled instances of the probe (script `Pins.lean` in `thms` mode, namespace `RBM.Gauss.T2002Inst`, output verbatim)

```
T2002Vocab.lean:1056 theorem RBM.Gauss.T2002Inst.sz0_values : RBM.Gauss.T2002Inst.sz0.L 0 = 4 ∧  RBM.Gauss.T2002Inst.sz0.W 0 = 32 ∧ RBM.Gauss.T2002Inst.sz0.size 0 = 2097152 ∧ RBM.Gauss.T2002Inst.sz0.lam 0 = 1 / 64
T2002Vocab.lean:1061 theorem RBM.Gauss.T2002Inst.sz0_L_le_W : ∀ (n : ℕ), RBM.Gauss.T2002Inst.sz0.L n ≤ RBM.Gauss.T2002Inst.sz0.W n
T2002Vocab.lean:1069 theorem RBM.Gauss.T2002Inst.sz0_size_le_W_pow : ∀ (n : ℕ), RBM.Gauss.T2002Inst.sz0.size n ≤ RBM.Gauss.T2002Inst.sz0.W n ^ 6
T2002Vocab.lean:1077 theorem RBM.Gauss.T2002Inst.sz0_bandwidth_at : ∀ (n : ℕ), ↑(RBM.Gauss.T2002Inst.sz0.size n) ^ (1 / 6) ≤ ↑(RBM.Gauss.T2002Inst.sz0.W n)
T2002Vocab.lean:1087 theorem RBM.Gauss.T2002Inst.sz0_bandwidth : RBM.Gauss.T2002Inst.sz0.Bandwidth (1 / 6)
T2002Vocab.lean:1089 theorem RBM.Gauss.T2002Inst.sz0_tendsto : RBM.Gauss.T2002Inst.sz0.SizeTendsto
T2002Vocab.lean:1100 theorem RBM.Gauss.T2002Inst.sz0_WO : RBM.Gauss.T2002Inst.sz0.WO (1 / 10)
T2002Vocab.lean:1118 theorem RBM.Gauss.T2002Inst.sz0_admissible : RBM.Gauss.T2002Inst.sz0.Admissible (1 / 6) (1 / 10)
T2002Vocab.lean:1123 theorem RBM.Gauss.T2002Inst.sz0_lam_sq : ∀ᶠ (n : ℕ) in Filter.atTop,  ↑(RBM.Gauss.T2002Inst.sz0.W n) ^ (2 * (1 / 10)) ≤   RBM.Gauss.T2002Inst.sz0.lam n ^ 2 * ↑(RBM.Gauss.T2002Inst.sz0.W n) ^ 3
T2002Vocab.lean:1129 theorem RBM.Gauss.T2002Inst.scales_sz0 : RBM.ellT 4 (1 / 64) 0 = 1 ∧  RBM.Bparam 3 4 (1 / 64) 0 0 = ((1 / 64) ^ 2 + 1)⁻¹ + (4 ^ 3)⁻¹ ∧ 0 < RBM.Gauss.T2002Inst.sz0.Bctl 0 0
T2002Vocab.lean:1143 theorem RBM.Gauss.T2002Inst.sz0_lam_tendsto : Filter.Tendsto RBM.Gauss.T2002Inst.sz0.lam Filter.atTop (nhds 0)
T2002Vocab.lean:1162 theorem RBM.Gauss.T2002Inst.sz0_size_pos : 1 < ↑(RBM.Gauss.T2002Inst.sz0.size 0)
T2002Vocab.lean:1165 theorem RBM.Gauss.T2002Inst.z0_im_pos : 0 < RBM.Gauss.T2002Inst.z0.im
T2002Vocab.lean:1168 theorem RBM.Gauss.T2002Inst.z0_mem : RBM.Gauss.T2002Inst.sz0.locDomain (1 / 10) (1 / 10) 0 RBM.Gauss.T2002Inst.z0
T2002Vocab.lean:1175 theorem RBM.Gauss.T2002Inst.z0_zztE : (|RBM.lemE RBM.Gauss.T2002Inst.z0| ≤ 2 - 1 / 10 ∧   1 / 16 ≤ RBM.lemT RBM.Gauss.T2002Inst.z0 ∧    1 / 16 * RBM.Gauss.T2002Inst.z0.im ≤      (RBM.zt (RBM.lemE RBM.Gauss.T2002Inst.z0) (RBM.lemT RBM.Gauss.T2002Inst.z0)).im ∧     (RBM.zt (RBM.lemE RBM.Gauss.T2002Inst.z0) (RBM.lemT RBM.Gauss.T2002Inst.z0)).im ≤      (1 / 16)⁻¹ * RBM.Gauss.T2002Inst.z0.im) ∧  RBM.msc RBM.Gauss.T2002Inst.z0 = ↑√(RBM.lemT RBM.Gauss.T2002Inst.z0) * RBM.mE (RBM.lemE RBM.Gauss.T2002Inst.z0) ∧   RBM.Gauss.T2002Inst.z0 =    (↑√(RBM.lemT RBM.Gauss.T2002Inst.z0))⁻¹ *     RBM.zt (RBM.lemE RBM.Gauss.T2002Inst.z0) (RBM.lemT RBM.Gauss.T2002Inst.z0)
T2002Vocab.lean:1187 theorem RBM.Gauss.T2002Inst.z0_Gt : ∀ (ω : RBM.Gauss.T2002Inst.sz0.SeqΩ),  ↑√(RBM.lemT RBM.Gauss.T2002Inst.z0) •    RBM.Gauss.T2002Inst.sz0.Gt 0 (RBM.lemE RBM.Gauss.T2002Inst.z0) (RBM.lemT RBM.Gauss.T2002Inst.z0) true ω =   RBM.Gauss.T2002Inst.sz0.Gn 0 RBM.Gauss.T2002Inst.z0 ω
T2002Vocab.lean:1194 theorem RBM.Gauss.T2002Inst.svarF_sz0 : RBM.Gauss.svarF 3 4 32 (1 / 64) 0 0 = (32 ^ 3)⁻¹ * (1 + 2 * 3 * (1 / 64) ^ 2)⁻¹
T2002Vocab.lean:1199 theorem RBM.Gauss.T2002Inst.svarF_sz0_pos : 0 < RBM.Gauss.svarF 3 4 32 (1 / 64) 0 0
T2002Vocab.lean:1202 theorem RBM.Gauss.T2002Inst.card_Iblk_sz0 : ∀ (a : RBM.Zd 3 4), (RBM.Gauss.Iblk 3 4 32 a).card = 32768
T2002Vocab.lean:1206 theorem RBM.Gauss.T2002Inst.card_Idx_sz0 : Fintype.card (RBM.Gauss.Idx 3 (RBM.Gauss.T2002Inst.sz0.L 0) (RBM.Gauss.T2002Inst.sz0.W 0)) = 2097152
T2002Vocab.lean:1210 theorem RBM.Gauss.T2002Inst.zdistInf_inst : RBM.Gauss.zdistInf 3 4 ![2, 1, 3] = 2 ∧ RBM.zdistD 3 4 ![2, 1, 3] = 4
T2002Vocab.lean:1216 theorem RBM.Gauss.T2002Inst.seqP_sz0_prob : MeasureTheory.IsProbabilityMeasure RBM.Gauss.T2002Inst.sz0.seqP
T2002Vocab.lean:1219 theorem RBM.Gauss.T2002Inst.seqP_sz0_slice : MeasureTheory.Measure.map (RBM.Gauss.T2002Inst.sz0.slice 0) RBM.Gauss.T2002Inst.sz0.seqP =  RBM.Gauss.PF 3 (RBM.Gauss.T2002Inst.sz0.L 0) (RBM.Gauss.T2002Inst.sz0.W 0) (RBM.Gauss.T2002Inst.sz0.lam 0)
T2002Vocab.lean:1224 theorem RBM.Gauss.T2002Inst.seqXmat_sz0_herm : ∀ (ω : RBM.Gauss.T2002Inst.sz0.SeqΩ), (RBM.Gauss.T2002Inst.sz0.seqXmat 0 ω).IsHermitian
T2002Vocab.lean:1233 theorem RBM.Gauss.T2002Inst.Eseq_abs_lt : ∀ (n : ℕ), |RBM.Gauss.T2002Inst.Eseq n| < 2
T2002Vocab.lean:1238 theorem RBM.Gauss.T2002Inst.Gt_prec : RBM.Gauss.T2002Inst.sz0.Prec  (fun (n : ℕ) (x : Unit) (ω : RBM.Gauss.T2002Inst.sz0.SeqΩ) ↦   ‖RBM.Gauss.T2002Inst.sz0.Gt n (RBM.Gauss.T2002Inst.Eseq n) (1 / 2) true ω 0 0‖)  fun (n : ℕ) (x : Unit) (x_1 : RBM.Gauss.T2002Inst.sz0.SeqΩ) ↦ (RBM.Gauss.etaT (RBM.Gauss.T2002Inst.Eseq n) (1 / 2))⁻¹
T2002Vocab.lean:1255 theorem RBM.Gauss.T2002Inst.Gt_whp : RBM.Gauss.T2002Inst.sz0.Whp fun (n : ℕ) ↦  {ω : RBM.Gauss.T2002Inst.sz0.SeqΩ |   ∀ (_u : Unit),    ‖RBM.Gauss.T2002Inst.sz0.Gt n (RBM.Gauss.T2002Inst.Eseq n) (1 / 2) true ω 0 0‖ ≤     ↑(RBM.Gauss.T2002Inst.sz0.size n) ^ (1 / 10) * (RBM.Gauss.etaT (RBM.Gauss.T2002Inst.Eseq n) (1 / 2))⁻¹}
T2002Vocab.lean:1261 theorem RBM.Gauss.T2002Inst.localLaw_sz0 : RBM.Gauss.T2002Inst.sz0.LocalLawPT RBM.Gauss.T2002Inst.Eseq (fun (x : ℕ) ↦ 1 / 2) fun (n : ℕ) ↦  2 * (RBM.Gauss.etaT (RBM.Gauss.T2002Inst.Eseq n) (1 / 2))⁻¹
T2002Vocab.lean:1294 theorem RBM.Gauss.T2002Inst.gridRes_prec : RBM.Gauss.T2002Inst.sz0.PrecGrid  (fun (n : ℕ) (x : Unit) (ω : RBM.Path.PathΩ RBM.Gauss.T2002Inst.sz0) ↦   ‖RBM.Gauss.Gres     (RBM.Path.pathH RBM.Gauss.T2002Inst.sz0 (fun (x : ℕ) ↦ 0) (fun (x : ℕ) ↦ 1 / 2) (fun (x : ℕ) ↦ 4) n 2 ω)     (RBM.zt (RBM.Gauss.T2002Inst.Eseq n) (1 / 2)) true 0 0‖)  fun (n : ℕ) (x : Unit) (x_1 : RBM.Path.PathΩ RBM.Gauss.T2002Inst.sz0) ↦  (RBM.Gauss.etaT (RBM.Gauss.T2002Inst.Eseq n) (1 / 2))⁻¹
T2002Vocab.lean:1312 theorem RBM.Gauss.T2002Inst.Gt_timeIcc_prec : RBM.Gauss.T2002Inst.sz0.PrecPT  (fun (n : ℕ) (u : RBM.Path.TimeIcc (fun (x : ℕ) ↦ 0) (fun (x : ℕ) ↦ 1 / 2) n) (ω : RBM.Gauss.T2002Inst.sz0.SeqΩ) ↦   ‖RBM.Gauss.T2002Inst.sz0.Gt n (RBM.Gauss.T2002Inst.Eseq n) (↑u) true ω 0 0‖)  fun (n : ℕ) (u : RBM.Path.TimeIcc (fun (x : ℕ) ↦ 0) (fun (x : ℕ) ↦ 1 / 2) n) (x : RBM.Gauss.T2002Inst.sz0.SeqΩ) ↦  (RBM.Gauss.etaT (RBM.Gauss.T2002Inst.Eseq n) ↑u)⁻¹
T2002Vocab.lean:1331 theorem RBM.Gauss.T2002Inst.loop_envelope : ∀ (ω : RBM.Gauss.Omega 3 4 32),  ‖RBM.Gauss.loopM 3 4 32 (RBM.Gauss.Hmat 3 4 32 ω) (RBM.zt (1 / 2) (1 / 2)) ![true, false] ![0, 0]‖ ≤   (RBM.Gauss.etaT (1 / 2) (1 / 2))⁻¹ ^ 2
T2002Vocab.lean:1339 theorem RBM.Gauss.T2002Inst.loopL_sz0 : ∀ (ω : RBM.Gauss.Omega 3 4 32),  RBM.Gauss.loopL 3 4 32 (RBM.Gauss.Hmat 3 4 32 ω) (RBM.zt (1 / 2) (1 / 2)) (RBM.Gauss.loopOf ![true, false] ![0, 0]) =   RBM.Gauss.loopM 3 4 32 (RBM.Gauss.Hmat 3 4 32 ω) (RBM.zt (1 / 2) (1 / 2)) ![true, false] ![0, 0]
T2002Vocab.lean:1346 theorem RBM.Gauss.T2002Inst.Mres_sz0 : RBM.Gauss.Mres 0 RBM.Gauss.T2002Inst.z0 (RBM.msc RBM.Gauss.T2002Inst.z0) = RBM.msc RBM.Gauss.T2002Inst.z0 • 1
T2002Vocab.lean:1353 theorem RBM.Gauss.T2002Inst.Lloop_sz0 : ∀ (ω : RBM.Gauss.T2002Inst.sz0.SeqΩ) (a : RBM.Zd 3 (RBM.Gauss.T2002Inst.sz0.L 0)),  RBM.Gauss.T2002Inst.sz0.Lloop 0 (1 / 2) 0 (fun (x : Fin 1) ↦ true) (fun (x : Fin 1) ↦ a) ω = RBM.mE (1 / 2)
T2002Vocab.lean:1362 theorem RBM.Gauss.T2002Inst.transfer_at : RBM.Path.TransferLaw RBM.Gauss.T2002Inst.sz0 →  MeasureTheory.Measure.map    (RBM.Path.pathH RBM.Gauss.T2002Inst.sz0 (fun (x : ℕ) ↦ 0) (fun (x : ℕ) ↦ 1 / 2) (fun (x : ℕ) ↦ 4) 0 2)    (RBM.Path.pathP RBM.Gauss.T2002Inst.sz0) =   MeasureTheory.Measure.map    (RBM.Gauss.T2002Inst.sz0.seqHflow 0     (RBM.Path.gridTime (fun (x : ℕ) ↦ 0) (fun (x : ℕ) ↦ 1 / 2) (fun (x : ℕ) ↦ 4) 0 2))    RBM.Gauss.T2002Inst.sz0.seqP
T2002Vocab.lean:1371 theorem RBM.Gauss.T2002Inst.indep_at : RBM.Path.IndepIncr RBM.Gauss.T2002Inst.sz0 →  ∀ (k : ℕ),   ProbabilityTheory.Indep (↑(RBM.Path.filt RBM.Gauss.T2002Inst.sz0) k)    (MeasurableSpace.comap (fun (ω : RBM.Path.PathΩ RBM.Gauss.T2002Inst.sz0) ↦ ω (k + 1)) inferInstance)    (RBM.Path.pathP RBM.Gauss.T2002Inst.sz0)
T2002Vocab.lean:1375 theorem RBM.Gauss.T2002Inst.pathP_sz0_prob : MeasureTheory.IsProbabilityMeasure (RBM.Path.pathP RBM.Gauss.T2002Inst.sz0)
T2002Vocab.lean:1377 theorem RBM.Gauss.T2002Inst.gridTime_sz0 : RBM.Path.gridTime (fun (x : ℕ) ↦ 0) (fun (x : ℕ) ↦ 1 / 2) (fun (x : ℕ) ↦ 4) 0 2 = 1 / 4
T2002Vocab.lean:1384 theorem RBM.Gauss.T2002Inst.Gt_BA_sz0 : ∀ (lam0 : ℕ → ℝ) (m0 : ℂ) (E t0 : ℝ),  0 < t0 →   lam0 0 = √t0 * RBM.Gauss.T2002Inst.sz0.lam 0 →    RBM.Gauss.ztOf m0 E t0 = ↑√t0 * RBM.Gauss.T2002Inst.z0 →     ∀ (ω : RBM.Gauss.T2002Inst.sz0.SeqΩ),      ↑√t0 • RBM.Gauss.Gres (RBM.Gauss.T2002Inst.sz0.seqHflowBA lam0 0 t0 ω) (RBM.Gauss.ztOf m0 E t0) true =       RBM.Gauss.Gres (RBM.Gauss.T2002Inst.sz0.seqHBA 0 ω) RBM.Gauss.T2002Inst.z0 true
T2002Vocab.lean:1396 theorem RBM.Gauss.T2002Inst.W_le_size_sz0 : ↑(RBM.Gauss.T2002Inst.sz0.W 0) ^ (1 / 10) ≤ ↑(RBM.Gauss.T2002Inst.sz0.size 0) ^ (1 / 10 / ↑3)
T2002Vocab.lean:1401 theorem RBM.Gauss.T2002Inst.size_le_W_sz0 : ↑(RBM.Gauss.T2002Inst.sz0.size 0) ^ (1 / 10) ≤ ↑(RBM.Gauss.T2002Inst.sz0.W 0) ^ (1 / 10 / (1 / 6))
```

## I. Mathlib names used by the probe (script `Names.lean`: `#check`, output verbatim, continuation lines joined)

```
@finFunctionFinEquiv : {m n : ℕ} → (Fin n → Fin m) ≃ Fin (m ^ n)
@MeasureTheory.Measure.infinitePi : {ι : Type u_1} → {X : ι → Type u_2} → {mX : (i : ι) → MeasurableSpace (X i)} → ((i : ι) → MeasureTheory.Measure (X i)) → MeasureTheory.Measure ((i : ι) → X i)
@MeasureTheory.Measure.eq_infinitePi : ∀ {ι : Type u_1} {X : ι → Type u_2} {mX : (i : ι) → MeasurableSpace (X i)} (μ : (i : ι) → MeasureTheory.Measure (X i)) [hμ : ∀ (i : ι), MeasureTheory.IsProbabilityMeasure (μ i)] {ν : MeasureTheory.Measure ((i : ι) → X i)}, (∀ (s : Finset ι) (t : (i : ι) → Set (X i)), (∀ (i : ι), MeasurableSet (t i)) → ν ((↑s).pi t) = ∏ i ∈ s, (μ i) (t i)) → ν = MeasureTheory.Measure.infinitePi μ
@MeasureTheory.Measure.infinitePi_pi : ∀ {ι : Type u_1} {X : ι → Type u_2} {mX : (i : ι) → MeasurableSpace (X i)} (μ : (i : ι) → MeasureTheory.Measure (X i)) [hμ : ∀ (i : ι), MeasureTheory.IsProbabilityMeasure (μ i)] {s : Finset ι} {t : (i : ι) → Set (X i)}, (∀ i ∈ s, MeasurableSet (t i)) → (MeasureTheory.Measure.infinitePi μ) ((↑s).pi t) = ∏ i ∈ s, (μ i) (t i)
ProbabilityTheory.gaussianReal : ℝ → NNReal → MeasureTheory.Measure ℝ
@MeasureTheory.Filtration.piLE : {ι : Type u_1} → [inst : Preorder ι] → {X : ι → Type u_2} → [inst_1 : (i : ι) → MeasurableSpace (X i)] → MeasureTheory.Filtration ι MeasurableSpace.pi
@Matrix.inv_smul : ∀ {n : Type u_1} {α : Type u_2} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : CommRing α] (A : Matrix n n α) (k : α) [inst_3 : Invertible k], IsUnit A.det → (k • A)⁻¹ = ⅟k • A⁻¹
@Matrix.nonsing_inv_eq_ringInverse : ∀ {n : Type u_1} {α : Type u_2} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : CommRing α] (A : Matrix n n α), A⁻¹ = Ring.inverse A
@Matrix.inv_eq_right_inv : ∀ {n : Type u_1} {α : Type u_2} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : CommRing α] {A B : Matrix n n α}, A * B = 1 → A⁻¹ = B
@Matrix.isUnit_iff_isUnit_det : ∀ {n : Type u_1} {α : Type u_2} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : CommRing α] (A : Matrix n n α), IsUnit A ↔ IsUnit A.det
@Matrix.IsHermitian.submatrix : ∀ {α : Type u_1} {m : Type u_2} {n : Type u_3} [inst : Star α] {A : Matrix n n α}, A.IsHermitian → ∀ (f : m → n), (A.submatrix f f).IsHermitian
@Matrix.conjTranspose_kronecker : ∀ {R : Type u_1} {l : Type u_2} {m : Type u_3} {n : Type u_4} {p : Type u_5} [inst : CommMagma R] [inst_1 : StarMul R] (x : Matrix l m R) (y : Matrix n p R), (Matrix.kroneckerMap (fun x1 x2 => x1 * x2) x y).conjTranspose = Matrix.kroneckerMap (fun x1 x2 => x1 * x2) x.conjTranspose y.conjTranspose
@Matrix.trace_diagonal : ∀ {R : Type u_1} [inst : AddCommMonoid R] {o : Type u_2} [inst_1 : Fintype o] [inst_2 : DecidableEq o] (d : o → R), (Matrix.diagonal d).trace = ∑ i, d i
@Real.pow_rpow_inv_natCast : ∀ {x : ℝ} {n : ℕ}, 0 ≤ x → n ≠ 0 → (x ^ n) ^ (↑n)⁻¹ = x
@Real.rpow_le_rpow_of_exponent_le : ∀ {x y z : ℝ}, 1 ≤ x → y ≤ z → x ^ y ≤ x ^ z
@Real.rpow_le_one_of_one_le_of_nonpos : ∀ {x z : ℝ}, 1 ≤ x → z ≤ 0 → x ^ z ≤ 1
@Filter.Tendsto.inv_tendsto_atTop : ∀ {𝕜 : Type u_1} {α : Type u_2} [inst : Semifield 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [inst_3 : TopologicalSpace 𝕜] [OrderTopology 𝕜] {l : Filter α} {f : α → 𝕜}, Filter.Tendsto f l Filter.atTop → Filter.Tendsto f⁻¹ l (nhds 0)
@Nat.le_self_pow : ∀ {n : ℕ}, n ≠ 0 → ∀ (a : ℕ), a ≤ a ^ n
@Fintype.bijective_iff_injective_and_card : ∀ {α : Type u_1} {β : Type u_2} [inst : Fintype α] [inst_1 : Fintype β] (f : α → β), Function.Bijective f ↔ Function.Injective f ∧ Fintype.card α = Fintype.card β
@Finset.card_equiv : ∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t : Finset β} (e : α ≃ β), (∀ (i : α), i ∈ s ↔ e i ∈ t) → s.card = t.card
@ZMod.val_natCast_of_lt : ∀ {n a : ℕ}, a < n → (↑a).val = a
@smul_mul_smul_comm : ∀ {α : Type u_1} {β : Type u_2} [inst : Mul α] [inst_1 : Mul β] [inst_2 : SMul α β] [IsScalarTower α β β] [IsScalarTower α α β] [SMulCommClass α β β] (a : α) (b : β) (c : α) (d : β), a • b * c • d = (a * c) • (b * d)
@Set.mem_ofPred_eq : ∀ {α : Type u_1} {x : α} {p : α → Prop}, (x ∈ {y | p y}) = p x
@Matrix.conjTranspose_sum : ∀ {m : Type u_2} {n : Type u_3} {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : StarAddMonoid α] {ι : Type u_4} (s : Finset ι) (M : ι → Matrix m n α), (∑ i ∈ s, M i).conjTranspose = ∑ i ∈ s, (M i).conjTranspose
@Matrix.IsHermitian.add : ∀ {α : Type u_1} {n : Type u_2} [inst : AddMonoid α] [inst_1 : StarAddMonoid α] {A B : Matrix n n α}, A.IsHermitian → B.IsHermitian → (A + B).IsHermitian
@Matrix.conjTranspose_smul : ∀ {m : Type u_2} {n : Type u_3} {R : Type u_4} {α : Type u_1} [inst : Star R] [inst_1 : Star α] [inst_2 : SMul R α] [StarModule R α] (c : R) (M : Matrix m n α), (c • M).conjTranspose = star c • M.conjTranspose
@Real.one_le_rpow : ∀ {x z : ℝ}, 1 ≤ x → 0 ≤ z → 1 ≤ x ^ z
@MeasureTheory.measure_empty : ∀ {α : Type u_1} {F : Type u_2} [inst : FunLike F (Set α) ENNReal] [MeasureTheory.OuterMeasureClass F α] {μ : F}, μ ∅ = 0
```

## J. Scripts (verbatim; run in this order: `closure.py > closure.tsv`, `labels.py > texlabels.tsv`, `stats.py > stats.tsv`, `headlines.py <commit> > headlines.tsv`; `final_run.py` (every command whose output the reports paste, with `Inv.lean`, `Pins.lean`, `Pins_thms.lean` = `Pins.lean` with the last line `#pins thms RBM.Gauss.T2002Inst`, `Names.lean`, `Clash.lean` under `lake env lean`), `final_extra.py`, `postproc.py`, `mkportmap.py md <out>`, `mkreport3.py`; `inv.py` as in A.2, `invcompact.py` for the compact inventory)

### J.inv.py

```
#!/usr/bin/env python3
"""Inventory of public definitions of a Lean file at a git ref.
usage: inv.py REPO REF FILE [FILE...] [--sig N] [--theorems]
Prints: FILE<TAB>LINES<TAB>NDEF<TAB>NTHM  and, per def, `  L<line> <kind> <fullname> <signature>`.
A declaration is public iff it is not `private` (and not `protected`-free: protected stays public).
"""
import subprocess, sys, re

KINDS = ('def', 'abbrev', 'structure', 'class', 'inductive', 'instance', 'opaque', 'irreducible_def')
THM = ('theorem', 'lemma')
MODS = ('noncomputable', 'protected', 'private', 'partial', 'unsafe', 'nonrec')

def show(repo, ref, path):
    return subprocess.run(['git', '-C', repo, '--no-optional-locks', 'show', f'{ref}:{path}'],
                          capture_output=True, text=True, check=True).stdout

def strip_comments(text):
    # remove block comments (nested) keeping newlines, and line comments
    out = []; i = 0; depth = 0; n = len(text)
    while i < n:
        if text.startswith('/-', i):
            depth += 1; i += 2
            continue
        if depth > 0 and text.startswith('-/', i):
            depth -= 1; i += 2
            continue
        if depth > 0:
            if text[i] == '\n': out.append('\n')
            i += 1; continue
        if text.startswith('--', i):
            j = text.find('\n', i)
            if j < 0: break
            i = j; continue
        out.append(text[i]); i += 1
    return ''.join(out)

def parse(text, sig_n):
    lines = strip_comments(text).split('\n')
    stack = []  # (kind, name)
    decls = []  # (line, kind, fullname, private, sig)
    i = 0
    while i < len(lines):
        ln = lines[i]
        s = ln.strip()
        m = re.match(r'^namespace\s+(\S+)', s)
        if m:
            stack.append(('ns', m.group(1))); i += 1; continue
        m = re.match(r'^section\b\s*(\S*)', s)
        if m and not s.startswith('section_'):
            stack.append(('sec', m.group(1))); i += 1; continue
        m = re.match(r'^end\b\s*(\S*)', s)
        if m and (s == 'end' or re.match(r'^end(\s+\S+)?$', s)):
            if stack: stack.pop()
            i += 1; continue
        # strip attributes
        t = re.sub(r'^(@\[[^\]]*\]\s*)+', '', s)
        toks = t.split()
        mods = []
        while toks and toks[0] in MODS:
            mods.append(toks.pop(0))
        if toks and (toks[0] in KINDS or toks[0] in THM):
            kind = toks[0]
            rest = ' '.join(toks[1:])
            # gather declaration text until ':=' or 'where' at depth 0 (max 25 lines)
            buf = rest; j = i
            def done(b):
                d = 0
                for k, ch in enumerate(b):
                    if ch in '([{⟨': d += 1
                    elif ch in ')]}⟩': d -= 1
                    elif d == 0 and b.startswith(':=', k): return k
                    elif d == 0 and b.startswith(' where', k): return k
                    elif d == 0 and b.startswith(' with', k) and kind=='instance': return k
                return -1
            while done(buf) < 0 and j + 1 < len(lines) and j - i < 40:
                j += 1; buf += ' ' + lines[j].strip()
            k = done(buf)
            sigtxt = buf[:k] if k >= 0 else buf
            sigtxt = re.sub(r'\s+', ' ', sigtxt).strip()
            if kind == 'instance':
                nm = sigtxt.split(' ')[0] if sigtxt and not sigtxt.startswith(':') else '<anon>'
                sg = sigtxt
            else:
                mm = re.match(r'^([^\s:({\[⟨]+)\s*(.*)$', sigtxt)
                nm = mm.group(1) if mm else '<?>'
                sg = mm.group(2) if mm else sigtxt
            # decl-name with namespace; handle `_root_`
            nss = [x[1] for x in stack if x[0] == 'ns']
            full = nm if nm.startswith('_root_.') else '.'.join(nss + [nm])
            full = full.replace('_root_.', '')
            decls.append((i + 1, kind, full, 'private' in mods, sg[:sig_n]))
            i = j + 1; continue
        i += 1
    return decls

def main():
    args = sys.argv[1:]
    sig_n = 100
    show_thm = False
    if '--sig' in args:
        k = args.index('--sig'); sig_n = int(args[k + 1]); del args[k:k + 2]
    if '--theorems' in args:
        args.remove('--theorems'); show_thm = True
    repo, ref, files = args[0], args[1], args[2:]
    for f in files:
        text = show(repo, ref, f)
        nl = len(text.split('\n')) - (1 if text.endswith('\n') else 0)
        ds = parse(text, sig_n)
        pub = [d for d in ds if d[1] in KINDS and not d[3]]
        thm = [d for d in ds if d[1] in THM]
        pthm = [d for d in thm if not d[3]]
        print(f'{f}\t{nl}\t{len(pub)}\t{len(pthm)}')
        for (ln, kind, full, priv, sg) in pub:
            print(f'  L{ln} {kind} {full} {sg}')
        if show_thm:
            for (ln, kind, full, priv, sg) in pthm:
                print(f'  L{ln} {kind} {full}')
main()
```

### J.invcompact.py

```
#!/usr/bin/env python3
"""Compact form of the two inventories (ticket item 1): one line per directory (RBM3D) / per vocabulary file or group (RBM2D).
usage: invcompact.py   (reads inv3d.out written by Inv.lean; runs inv.py for RBM2D at c9a24cf)"""
import re, subprocess, collections
R3 = '/Users/junyin/Lean_proof/RBM3D-wt/T2002'; R2 = '/Users/junyin/Lean_proof/RBM2D'
bymod = collections.OrderedDict()
for l in open('inv3d.out'):
    m = re.match(r'^(RBM3D\.[A-Za-z.]+):(\d+) (\S+) (\S+) : ', l)
    if m: bymod.setdefault(m.group(1), []).append(m.group(4).replace('RBM.Gauss.', '').replace('RBM.', ''))
mods = ['Defs.Block', 'Defs.Convolution', 'Defs.Domination', 'Defs.Lattice', 'Defs.Neighbours', 'Defs.Params', 'Defs.RadialSum', 'Defs.Semicircle', 'Defs.Shells', 'Defs.StochDom', 'Defs.Tail',
        'Gauss.Domination', 'Gauss.Envelope', 'Gauss.Model', 'Gauss.Stein', 'Gauss.SteinMatrix', 'Loop.GLoop', 'Analysis.Resolvent']
def nl3(m): return subprocess.run(['git', '-C', R3, 'show', 'main:RBM3D/' + m.replace('.', '/') + '.lean'], capture_output=True, text=True).stdout.count('\n')
grp = collections.OrderedDict()
for m in mods: grp.setdefault(m.split('.')[0], []).append(m)
print('RBM3D on main (3c11d7b): directory | files | lines | public defs | file(lines): names')
for d, ms in grp.items():
    names = {m: bymod.get('RBM3D.' + m, []) for m in ms}
    print(f"{d}: {len(ms)} files, {sum(nl3(m) for m in ms)} lines, {sum(len(v) for v in names.values())} defs | " +
          '; '.join(f"{m.split('.')[1]}({nl3(m)}):{' '.join(v) if v else '-'}" for m, v in names.items()))
def run(*a): return subprocess.run(a, capture_output=True, text=True, check=True).stdout
def inv(files):
    out = run('python3', 'inv.py', R2, 'c9a24cf', *files, '--sig', '60'); res = collections.OrderedDict(); cur = None
    for l in out.split('\n'):
        if not l: continue
        if not l.startswith('  '): f, n, nd, nt = l.split('\t'); cur = f; res[cur] = [int(n), int(nd), []]
        else: m = re.match(r'^  L(\d+) (\S+) (\S+)', l); res[cur][2].append(m.group(3).split('.')[-1])
    return res
def ls(d): return [x for x in run('git', '-C', R2, '--no-optional-locks', 'ls-tree', '-r', '--name-only', 'c9a24cf', '--', d).split('\n') if x.endswith('.lean')]
specs = [('RBM2D/Gauss/Model.lean', ['RBM2D/Gauss/Model.lean']), ('RBM2D/Defs/StochDom.lean', ['RBM2D/Defs/StochDom.lean']),
         ('RBM2D/Defs/Semicircle*.lean', ['RBM2D/Defs/Semicircle.lean', 'RBM2D/Defs/SemicircleIntegral.lean']), ('RBM2D/Path/Scales.lean', ['RBM2D/Path/Scales.lean']),
         ('RBM2D/Hierarchy/ (47 files)', ls('RBM2D/Hierarchy')), ('RBM2D/Induction/Defs.lean', ['RBM2D/Induction/Defs.lean']),
         ('RBM2D/Induction/HierVocab.lean', ['RBM2D/Induction/HierVocab.lean']), ('RBM2D/Evolution/Defs.lean', ['RBM2D/Evolution/Defs.lean']),
         ('RBM2D/Endpoints.lean', ['RBM2D/Endpoints.lean'])]
print('RBM2D c9a24cf: vocabulary file(s) | lines | public defs | first names')
for label, files in specs:
    r = inv(files); names = [n for v in r.values() for n in v[2]]
    print(f"{label}: {sum(v[0] for v in r.values())} lines, {sum(v[1] for v in r.values())} defs | " + ' '.join(names[:12]) + (f' ...(+{len(names) - 12})' if len(names) > 12 else ''))
```

### J.closure.py

```
#!/usr/bin/env python3
"""File-level import closure of RBM2D at c9a24cf from the endpoint modules.
Output TSV: path<TAB>lines<TAB>reachable(0/1)<TAB>imports_count
"""
import subprocess, re, sys, collections
repo='/Users/junyin/Lean_proof/RBM2D'; ref='c9a24cf'
def git(*a):
    return subprocess.run(['git','-C',repo,'--no-optional-locks',*a],capture_output=True,text=True,check=True).stdout
files=[x for x in git('ls-tree','-r','--name-only',ref,'--','RBM2D').split('\n') if x.endswith('.lean')]
text={f:git('show',f'{ref}:{f}') for f in files}
mod=lambda f: f[:-5].replace('/','.')
file_of={mod(f):f for f in files}
imps={}
for f,t in text.items():
    imps[f]=[m for m in re.findall(r'^import\s+(RBM2D\.[A-Za-z0-9_.]+)',t,re.M)]
roots=sys.argv[1:] or ['RBM2D/Main/Endpoints.lean','RBM2D/Main/BUnivHolds.lean']
seen=set(); q=collections.deque(roots)
while q:
    f=q.popleft()
    if f in seen: continue
    seen.add(f)
    for m in imps.get(f,[]):
        g=file_of.get(m)
        if g and g not in seen: q.append(g)
for f in sorted(files):
    n=len(text[f].split('\n'))-(1 if text[f].endswith('\n') else 0)
    print(f'{f}\t{n}\t{1 if f in seen else 0}\t{len(imps[f])}')
```

### J.labels.py

```
#!/usr/bin/env python3
import re, glob, os
root='/Users/junyin/Lean_proof/RBM3D/paper/tex'
out=[]
for f in sorted(glob.glob(root+'/*.tex')):
    b=os.path.basename(f)
    for i,l in enumerate(open(f,encoding='utf-8',errors='replace').read().split('\n'),1):
        s=l.lstrip()
        if s.startswith('%'): continue
        # strip trailing comment
        l2=re.sub(r'(?<!\\)%.*$','',l)
        for m in re.finditer(r'\\label\{([^}]*)\}',l2):
            out.append((m.group(1),b,i))
for lab,b,i in out: print(f'{lab}\t{b}:{i}')
```

### J.stats.py

```
#!/usr/bin/env python3
import subprocess, re, csv, sys
repo='/Users/junyin/Lean_proof/RBM2D'; ref='c9a24cf'
def git(*a):
    return subprocess.run(['git','-C',repo,'--no-optional-locks',*a],capture_output=True,text=True,check=True).stdout
clos={}
for l in open('closure.tsv'):
    p,n,r,i=l.rstrip('\n').split('\t'); clos[p]=(int(n),int(r))
tex=set(l.split('\t')[0] for l in open('texlabels.tsv'))
tok=[('Z2',r'\bZ2\b'),('zdist2',r'\bzdist2\b'),('Idx',r'\bIdx\b'),('Blk',r'\b(BlockIndex|Iblk|blk|splitEquiv|split|Eblk|Epaper|Svar|Spaper|SW)\b'),
 ('pow2',r'(\(W : ℝ\)|\(L : ℝ\)|\bW\b|\bL\b|\(W \* L\)|\(W : ℂ\)⁻¹|\(W : ℝ\)⁻¹|\(W : ℂ\)|\(\(W \* L\) \^ 2 : ℕ\)|size)\)?\s*\^\s*2\b'),
 ('sup2',r'(W|L|N)[⁻]?²|⁻²|\bd = 2\b|Z_L\^2|Z_\{WL\}\^2|\(W L\)²'),
 ('five',r'\b5⁻¹|\(1 / 5\)|1/5\b'),('log',r'Real\.log|\blog\b'),('Sizes',r'\bSizes\b|\bseqP\b|\bd\.(L|W|size)\b'),('scale',r'\bscaleM\b|\bellT\b|\btailT\b|\bellStar\b|\bMeta\b|\bellz\b')]
rows=[]
files=sorted(clos)
for f in files:
    t=git('show',f'{ref}:{f}')
    m=re.search(r'/-!(.*?)-/',t,re.S)
    head=m.group(1) if m else ''
    # labels cited in header: backticked tokens
    cands=set(re.findall(r'`\(?([A-Za-z][A-Za-z0-9_:;+\-<>=.\[\]\' ]*?)\)?`',head))
    cands2=set(x.strip() for x in cands)
    lab=sorted(c for c in cands2 if c in tex)
    # full-file labels too (cited in docstrings of decls)
    cands_f=set(x.strip() for x in re.findall(r'`\(?([A-Za-z][A-Za-z0-9_:;+\-<>=.\[\]\' ]*?)\)?`',t))
    labf=sorted(c for c in cands_f if c in tex and c not in lab)
    cnt={k:len(re.findall(p,t)) for k,p in tok}
    rows.append((f,clos[f][0],clos[f][1],cnt,lab,labf))
w=csv.writer(sys.stdout,delimiter='\t')
for f,n,r,cnt,lab,labf in rows:
    w.writerow([f,n,r]+[cnt[k] for k,_ in tok]+[','.join(lab[:12]),','.join(labf[:12])])
```

### J.headlines.py

```
#!/usr/bin/env python3
"""Line counts of every RBM2D file at the later commit HEAD (after RBM2D's own dead-code deletion T2274).
Output TSV: path<TAB>lines at HEAD or -1 if the file was deleted."""
import subprocess, sys
repo = '/Users/junyin/Lean_proof/RBM2D'
head = sys.argv[1]
def git(*a): return subprocess.run(['git', '-C', repo, '--no-optional-locks', *a], capture_output=True, text=True, check=True).stdout
new = set(x for x in git('ls-tree', '-r', '--name-only', head, '--', 'RBM2D').split('\n') if x.endswith('.lean'))
for l in open('closure.tsv'):
    p = l.split('\t')[0]
    if p in new:
        t = git('show', f'{head}:{p}'); print(f'{p}\t{t.count(chr(10))}')
    else:
        print(f'{p}\t-1')
```

### J.final_run.py

```
#!/usr/bin/env python3
"""Step 1 of the final generation: run every command whose output is pasted into the reports and save it
(with the command and its `date -u` start time) in outputs/<name>.txt.  Step 2 is mkreport.py."""
import subprocess, os, sys, re
WT = '/Users/junyin/Lean_proof/RBM3D-wt/T2002'
MAIN = '/Users/junyin/Lean_proof/RBM3D'
SC = os.path.dirname(os.path.abspath(__file__))
H = subprocess.run(['git', '-C', MAIN, 'rev-parse', '--short', 'main'], capture_output=True, text=True).stdout.strip()
open(f'{SC}/main_hash.txt', 'w').write(H + '\n')
os.makedirs(SC + '/outputs', exist_ok=True)
def sh(cmd, cwd, name, shell=True):
    t0 = subprocess.run(['date', '-u'], capture_output=True, text=True).stdout.strip()
    r = subprocess.run(cmd, cwd=cwd, shell=shell, capture_output=True, text=True, executable='/bin/zsh')
    out = (r.stdout + r.stderr)
    open(f'{SC}/outputs/{name}.txt', 'w').write(f'{t0}\n$ {cmd}\n{out}(exit {r.returncode})\n')
    return out, r.returncode
steps = [
 ('head', 'git rev-parse --short HEAD && git diff --stat main...t/T2002', WT),
 ('build', 'lake build RBM3D.Probe.T2002Vocab 2>&1 | grep -v "depends on axioms" | tail -3', WT),
 ('probe', f'lake env lean RBM3D/Probe/T2002Vocab.lean > {SC}/outputs/probe_raw.txt 2>&1; echo "exit=$?"; wc -l < {SC}/outputs/probe_raw.txt; '
           f'grep -c "depends on axioms: \\[propext, Classical.choice, Quot.sound\\]" {SC}/outputs/probe_raw.txt; '
           f'grep -vc "depends on axioms: \\[propext, Classical.choice, Quot.sound\\]" {SC}/outputs/probe_raw.txt; tail -2 {SC}/outputs/probe_raw.txt', WT),
 ('hygiene', 'grep -nE "sorry|admit|native_decide|^axiom " RBM3D/Probe/T2002Vocab.lean; echo "grep exit=$?"; wc -l RBM3D/Probe/T2002Vocab.lean', WT),
 ('clash_import', f'lake env lean {SC}/Clash.lean 2>&1 | tail -3', WT),
 ('pins_defs', f'lake env lean {SC}/Pins.lean', WT),
 ('pins_thms', f'lake env lean {SC}/Pins_thms.lean', WT),
 ('names', f'lake env lean {SC}/Names.lean', WT),
 ('inv3d', f'lake env lean {SC}/Inv.lean', WT),
 ('rbm2d', 'git -C ../RBM2D --no-optional-locks log --format="%h %s" c9a24cf..HEAD | cut -c1-150; '
           'echo "RBM2D HEAD: $(git -C ../RBM2D --no-optional-locks rev-parse --short HEAD); lines of diff --stat 0c1330a HEAD -- RBM2D RBM2D.lean: $(git -C ../RBM2D --no-optional-locks diff --stat 0c1330a HEAD -- RBM2D RBM2D.lean | wc -l | tr -d " ")"; '
           'git -C ../RBM2D --no-optional-locks diff --shortstat c9a24cf HEAD -- RBM2D RBM2D.lean; '
           'git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Gauss/Model.lean RBM2D/Defs/Model.lean RBM2D/Defs/StochDom.lean RBM2D/Gauss/Domination.lean RBM2D/Path/PerTime.lean RBM2D/Path/Walk.lean RBM2D/Path/Step2Props.lean RBM2D/Hierarchy/Loops.lean RBM2D/Endpoints.lean; '
           'for p in blockMat splitEquiv; do n=$(git -C ../RBM2D --no-optional-locks grep -c "$p" c9a24cf -- "RBM2D/*.lean" | awk -F: \'{s+=$NF} END{print s}\'); f=$(git -C ../RBM2D --no-optional-locks grep -l "$p" c9a24cf -- "RBM2D/*.lean" | wc -l | tr -d " "); echo "c9a24cf: $p: $n lines in $f files"; done', MAIN),
 ('mergeduse', f'git grep -lE "Vtx|Hmat|Omega d L W|Gauss.Model" {H} -- RBM3D | sed "s/^{H}://" | sort; git grep -nE "Vtx|Hmat|Gauss.Model" {H} -- RBM3D/Basic.lean RBM3D/Gauss/SteinMatrix.lean | sed "s/^{H}://" | cut -c1-110; git grep -nE "P d L W|Gauss[.]P[^A-Za-z]|P_map_update" {H} -- RBM3D | sed "s/^{H}://" | grep -v "^RBM3D/Gauss/Model.lean"; echo "uses of Gauss.P outside Gauss/Model.lean: exit=$?"', MAIN),
 ('mainmoved', f'git log --format="%h %s" --grep="^T2005" 3c11d7b..{H} | cut -c1-100; git diff --stat 3c11d7b {H} -- RBM3D RBM3D.lean | cut -c1-90; echo "public definitions in Defs/SemicircleIntegral.lean at {H}: $(git show {H}:RBM3D/Defs/SemicircleIntegral.lean | grep -cE "^(noncomputable )?(def|abbrev|structure|instance|class|inductive) ")"; git show {H}:RBM3D/Defs/SemicircleIntegral.lean | grep -nE "^(theorem|lemma) " | cut -c1-110', MAIN),
 ('locsc', 'git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Endpoints.lean | sed -n "99p;102p;104p" | cut -c1-110; sed -n "389p" paper/tex/1_2_Intro_model_result.tex | cut -c1-150', MAIN),
 ('pins_central', f'lake env lean {SC}/Pins.lean | sed "s/T2002Vocab.lean://" | grep -E "^[0-9]+ (def|structure) RBM\\\\.(Gauss\\\\.|Path\\\\.)?(Sizes|Sizes\\\\.(size|WO|Admissible|seqP|seqHflow|Gt|Lloop|Prec|PrecPT|PrecGrid|Whp|seqHflowBA|LocalLawPT)|Xmat|ztOf|Gres|Mres|loopM|blockMat|pathH|TransferLaw) :" | sed "s/RBM\\\\.Gauss\\\\.//g; s/MeasureTheory\\\\.//g" | cut -c1-205', WT),
 ('inst_central', f'lake env lean {SC}/Pins_thms.lean | sed "s/T2002Vocab.lean://" | grep -E "^[0-9]+ theorem RBM\\\\.Gauss\\\\.T2002Inst\\\\.(sz0_admissible|sz0_lam_tendsto|z0_mem|z0_zztE|Gt_prec|localLaw_sz0|gridRes_prec|Gt_timeIcc_prec|card_Idx_sz0|Lloop_sz0|loop_envelope|transfer_at|Gt_BA_sz0) :" | sed "s/RBM\\\\.Gauss\\\\.T2002Inst\\\\.//g; s/RBM\\\\.Gauss\\\\.//g; s/RBM\\\\.Path\\\\.//g; s/MeasureTheory\\\\.//g" | cut -c1-215', WT),
]
if __name__ == '__main__':
    only = sys.argv[1:]          # optional: names of the steps to run (default: all steps)
    for name, cmd, cwd in steps:
        if only and name not in only: continue
        out, rc = sh(cmd, cwd, name)
        print(name, 'exit', rc, len(out.split('\n')), 'lines')
```

### J.final_extra.py

```
#!/usr/bin/env python3
"""Cheap evidence commands (no Lean) saved like final_run.py does."""
import subprocess, os
WT = '/Users/junyin/Lean_proof/RBM3D-wt/T2002'
MAIN = '/Users/junyin/Lean_proof/RBM3D'
SC = os.path.dirname(os.path.abspath(__file__))
def sh(cmd, cwd, name):
    t0 = subprocess.run(['date', '-u'], capture_output=True, text=True).stdout.strip()
    r = subprocess.run(cmd, cwd=cwd, shell=True, capture_output=True, text=True, executable='/bin/zsh')
    open(f'{SC}/outputs/{name}.txt', 'w').write(f'{t0}\n$ {cmd}\n{r.stdout}{r.stderr}(exit {r.returncode})\n')
    print(name, r.returncode)
sh('grep -nE "3 ≤ d|0 < d|^  (lam|three_le_L) : " RBM3D/Probe/T2002Vocab.lean | cut -c1-90', WT, 'hardc')
sh('sed -n "515p;1211p" paper/tex/1_2_Intro_model_result.tex | cut -c1-200', MAIN, 'apcorr')
sh('sed -n "14,15p;71p" RBM3D/Defs/Lattice.lean | cut -c1-110', WT, 'latt')
sh(f'lake env lean {SC}/Deprec.lean 2>&1 | grep -o "warning: .*" | cut -c1-120', WT, 'deprec')
```

### J.postproc.py

```
#!/usr/bin/env python3
"""Turn outputs/<name>.txt (date line, `$ cmd` line, output, `(exit n)` line) into the plain output files used by mkportmap.py."""
import re
def body(name):
    t = open(f'outputs/{name}.txt').read().split('\n')
    assert t[1].startswith('$ ')
    # drop date, command, trailing "(exit n)" and empty tail
    b = t[2:]
    while b and b[-1] == '': b.pop()
    assert b[-1].startswith('(exit'), b[-1]
    return b[:-1]
for name, out in [('pins_defs', 'pins_defs.out'), ('pins_thms', 'pins_thms.out'), ('inv3d', 'inv3d.out')]:
    b = [l for l in body(name) if l.strip()]
    if name != 'inv3d':
        b = [l for l in b if not re.search(r'\.eq_1 :', l)]
    open(out, 'w').write('\n'.join(b) + '\n')
b = '\n'.join(body('names')).strip()
ents = re.split(r'\n(?=[@A-Za-z_][^\n]* :)', b)
open('names.out', 'w').write('\n'.join(' '.join(e.split()) for e in ents) + '\n')
print('ok')
```

### J.mkportmap.py

```
#!/usr/bin/env python3
"""Port map RBM2D (c9a24cf) -> RBM3D: classification of every file of the nine stochastic directories.
Inputs (produced by closure.py, stats.py, labels.py in this directory):
  closure.tsv : path, lines, reachable-from-endpoints(0/1), #imports
  stats.tsv   : path, lines, reachable, Z2, zdist2, Idx, Blk, pow2, sup2, five, log, Sizes, hdrlabels, filelabels
  texlabels.tsv : label, file:line   (labels of the d>=3 paper TeX)
Output: markdown rows (stdout) and summary.json.
Class: a = dimension-free (copy with renaming R1-R4); b = generalize Z2->Zd, W^2->W^d, (WL)^2->(WL)^d, S^(B)(g), redo exponents;
       c = d=2-specific argument, replace by the d>=3 argument (label named); d = not needed (unreachable from the endpoints,
       or already in merged RBM3D).
"""
import sys, re, json, collections

stats = {}
for l in open('stats.tsv'):
    f = l.rstrip('\n').split('\t')
    stats[f[0]] = dict(lines=int(f[1]), reach=int(f[2]), Z2=int(f[3]), zdist2=int(f[4]), Idx=int(f[5]), Blk=int(f[6]),
                       pow2=int(f[7]), sup2=int(f[8]), five=int(f[9]), log=int(f[10]), Sizes=int(f[11]),
                       scale=int(f[12]),
                       hdr=[x for x in f[13].split(',') if x] if len(f) > 13 else [],
                       full=[x for x in f[14].split(',') if x] if len(f) > 14 else [])
headl = {}
for l in open('headlines.tsv'):
    p, n = l.rstrip('\n').split('\t'); headl[p] = int(n)
texpos = {}
for l in open('texlabels.tsv'):
    lab, pos = l.rstrip('\n').split('\t'); texpos.setdefault(lab, pos)
short = {'1_2_Intro_model_result.tex': '1_2', '3_5_Loop_Hierarchy.tex': '3_5', '6_Step6_two_loop.tex': '6',
         '7_8_light_weight.tex': '7_8', 'A_deterministic_estimates.tex': 'A', 'B_graphical_lemmas.tex': 'B',
         'main.tex': 'main'}
def lab_str(labs):
    out = []
    for x in labs:
        p = texpos.get(x)
        if p:
            fn, ln = p.split(':'); out.append(f'{x}@{short.get(fn, fn)}:{ln}')
    return out

# ---- rule tables -------------------------------------------------------------------------------
MERGED = {  # class d: already in merged RBM3D (target = the merged file)
 'RBM2D/Defs/Block.lean': 'RBM3D/Defs/Block.lean (SB, sbKernel, sbKernelR)',
 'RBM2D/Defs/Dist.lean': 'RBM3D/Defs/Lattice.lean (zdist, zdistD); `zdistInf` pinned in the probe',
 'RBM2D/Defs/Domination.lean': 'RBM3D/Defs/Domination.lean (UnifDetDom, DetDom)',
 'RBM2D/Defs/Semicircle.lean': 'RBM3D/Defs/Semicircle.lean (msc, lemE, lemT, mE, zt); `ellz`, `Meta` (d=2) replaced by merged Defs/Params.lean (ellT, Bparam)',
 'RBM2D/Defs/SemicircleIntegral.lean': 'RBM3D/Defs/SemicircleIntegral.lean (ported by T2005, merged on main after the branch point of this ticket: theorem msc_eq_integral)',
 'RBM2D/Gauss/Stein.lean': 'RBM3D/Gauss/Stein.lean',
 'RBM2D/Path/TailSums.lean': 'RBM3D/Defs/RadialSum.lean, Defs/Convolution.lean, Kernel/PropT.lean (lem:propT, d>=3 tail sums)',
 'RBM2D/Path/ScalesBridge.lean': 'none: RBM3D has the single merged ellT/etaT',
 'RBM2D/Hierarchy/OperationsPair.lean': 'RBM3D/Loop/TreeRep.lean (LoopIdx.cutGlueL, cutGlueR)',
}
# class c: d=2-specific argument; value = (replacement labels of the d>=3 paper, note)
STEP2 = ('eq:def2_stopping@3_5:533, Gronwall_inequality@3_5:493, eq:Gronwall_dervJuD@3_5:529, defCALJ@3_5:365, '
         'lem:newKLK@3_5:371, lem:LWterm@3_5:385, lem: EMn2_N@3_5:427, Eq:Gdecay_w@1_2:1349')
STEP6 = 'lem:improve_exp_aver@6:12, lem:LWterm_EXP@6:83, eq:ExpLWn=2@6:85, int_K-L+QE@6:109'
C = {}
for f in ['GoodEvent', 'GoodEventClose', 'GoodEventGrid', 'GoodSet', 'StepBound', 'Step2Grid', 'Step2Close', 'Step2Local',
          'Step2PropsV3', 'Step2Vocab', 'StepArith', 'Bootstrap', 'DriftPoint', 'TimeSums']:
    C[f'RBM2D/Path/{f}.lean'] = (STEP2, 'Step 2 stopping/Gronwall argument is d>=3-specific (DECISIONS §7)')
C['RBM2D/Induction/Step2TargetV3.lean'] = (STEP2, 'Step 2 target pin (route (D) near exponent 3): re-pin for d>=3')
for f in ['Step61', 'MLExpVocab', 'MLExpHier', 'MLExpDuhamel', 'MLExpDrift', 'MLExpInv', 'MLExpQ']:
    C[f'RBM2D/Evolution/{f}.lean'] = (STEP6, 'Step 6 (ML:exp) of d>=3 rests on the diagrammatic light-weight estimate (sec. 7, lem:LWterm_EXP), which no sister project has (DECISIONS §2 item 3)')
C['RBM2D/Green/Stability.lean'] = ('lem_propTH(4)@1_2:1140, eq:THETAinftinf@1_2:1141, eq:latticesum_d3 (merged Kernel/SumDecay.lean)',
                                   'Kstab2 = O(1+log L) is a d=2 lattice sum; d>=3 stability constant differs')
C['RBM2D/Path/Scales.lean'] = ('eq:ellt@1_2:1121, eq_B_param@1_2:1107, con_st_ind@1_2:1296 (merged Defs/Params.lean: ellT, Bparam)',
                               'M_u = W^2 l_u^2 eta_u and l_u = min((1-u)^(-1/2),L) are d=2 scales; control is W^{-d}B_{t,0}')
C['RBM2D/Induction/ScaleFacts.lean'] = ('con_st_ind@1_2:1296, eq:ellt@1_2:1121, eq_B_param@1_2:1107',
                                        'scale facts on M_u (d=2); redo on W^{-d}B_{t,0}')
# class a overrides (token rule would say b): dimension-free generic probability/algebra
A_FORCE = {
 'RBM2D/Defs/StochDom.lean': 'merged Defs/StochDom.lean covers the index-scale part; port StochDomAt/NormStochDom variants/Absorb section',
 'RBM2D/Gauss/Domination.lean': 'moment => domination bridge, generic; merged Gauss/Domination.lean has the index-scale part; port the *At variants',
 'RBM2D/Gauss/Envelope.lean': 'deterministic envelope, generic; merged Gauss/Envelope.lean has the index-scale part',
 'RBM2D/Gauss/SteinMatrix.lean': 'resampling/Stein for a countable product measure; merged SteinMatrix.lean covers the finite-pi part',
 'RBM2D/Hierarchy/Operations.lean': 'single-edge cut-and-glue `cutGlue` of Def:oper_loop on LoopIdx (Operations.lean:27); merged TreeRep has only cutGlueL/R',
 'RBM2D/Path/Azuma.lean': 'generic Azuma/Doob on any probability space',
 'RBM2D/Path/Markov.lean': 'generic grid Markov property on the walk carrier',
 'RBM2D/Path/Stop.lean': 'generic grid stopping times',
 'RBM2D/Path/Walk.lean': 'grid walk carrier over Sizes.SeqOmega: depends on d only through Sizes',
 'RBM2D/Path/PerTime.lean': 'per-time domination interface; generic in the scale',
 'RBM2D/Path/Transfer.lean': 'per-time transfer between grid walk and single-time model',
 'RBM2D/Gauss/LinearForm.lean': 'linear forms in the Gaussian coordinates of seqP',
}
# deleted by RBM2D T2274 but needed if the RBM3D endpoints keep the paper's union over z inside P (1_2:388-393)
KEEP_DESPITE_T2274 = {
 'RBM2D/Path/NetLift.lean': 'deleted by RBM2D T2274 as dead code (not reached from RBM2D\'s endpoint `locSC`, whose `forall z` is outside the probability); needed if the RBM3D endpoint keeps the paper\'s intersection over z inside P (1_2:388-393): net lift per time -> uniform in u',
 'RBM2D/Main/RegionUnif.lean': 'deleted by RBM2D T2274 as dead code (same reason); needed for the same purpose: union over the spectral region inside P',
}
B_FORCE = {
 'RBM2D/Evolution/LatticeSums.lean': 'mixed lattice sum over Z_L^2 (eq-1sum, 7:206): d enters through the shell count; redo with merged Defs/Shells.lean, RadialSum.lean',
}
TARGET_DIR = {'Defs': 'RBM3D/Defs', 'Gauss': 'RBM3D/Gauss', 'Green': 'RBM3D/Green', 'Hierarchy': 'RBM3D/Hierarchy',
              'Path': 'RBM3D/Path', 'Induction': 'RBM3D/Induction', 'Evolution': 'RBM3D/Evolution',
              'Main': 'RBM3D/Main', 'Universality': 'RBM3D/Universality'}
# labels of the d>=3 paper by directory, added to the cited ones when the file cites none
DEFAULT_LABELS = {
 'Green': 'lem_GbEXP@3_5:14, lem_ConArg@3_5:42',
 'Hierarchy': 'Def:G_loop@1_2:811, Def:oper_loop@1_2:905, lem:SE_basic@1_2:949',
 'Universality': 'Thm: B_Univ@1_2:452',
 'Main': 'MR:decol@1_2:357, MR:locSC@1_2:386, MR:QUE@1_2:406, MR:QuDiff@1_2:488',
}

def classify(path, st):
    d = path.split('/')[1]
    if path in MERGED:
        return 'd', MERGED[path], 'superseded by merged RBM3D', ''
    if path in C:
        lab, note = C[path]
        return 'c', f'{TARGET_DIR[d]}/{path.split("/")[-1]} (re-written)', note, lab
    if not st['reach']:
        return 'd', 'none', 'unreachable from Main/Endpoints.lean + Main/BUnivHolds.lean (import closure)', ''
    if headl.get(path, 0) < 0 and path not in KEEP_DESPITE_T2274:
        return 'd', 'none', 'deleted by RBM2D T2274 (dead code of the final d=2 proof, commit 99d6fe0)', ''
    tgt = f'{TARGET_DIR[d]}/{path.split("/", 2)[2]}'
    if path in A_FORCE:
        return 'a', tgt, A_FORCE[path], ''
    exp = st['pow2'] + st['sup2'] + st['five']
    if path in B_FORCE:
        return 'b', tgt, B_FORCE[path], ''
    if path in KEEP_DESPITE_T2274:
        return 'b', tgt, KEEP_DESPITE_T2274[path], ''
    if exp == 0 and st['scale'] > 0:
        return 'b', tgt, (f'no exponent token but {st["scale"]} uses of the d=2 scales (scaleM, ellT, tailT, Meta, ellz): '
                          'replace by ell_t (eq:ellt), B_{t,K} (eq_B_param), W^{-d}B_{t,0}'), ''
    if exp == 0:
        lat = st['Z2'] + st['zdist2'] + st['Idx'] + st['Blk']
        return 'a', tgt, f'no exponent token; renaming R1-R4 only (lattice tokens {lat}, Sizes tokens {st["Sizes"]})', ''
    return 'b', tgt, f'exponent tokens {exp} (W^2/L^2/N=(WL)^2/5^-1/d=2); Z2->Zd, W^2->W^d, S^(B)(g)', ''

rows = []
for path in sorted(stats):
    d = path.split('/')[1]
    if d not in TARGET_DIR: continue
    st = stats[path]
    cl, tgt, basis, lab = classify(path, st)
    labs = lab_str(st['hdr'] + st['full'])
    if lab: labs = [lab] + labs
    elif not labs and d in DEFAULT_LABELS and cl != 'd': labs = [DEFAULT_LABELS[d] + ' (dir default)']
    rows.append((path, st['lines'], cl, tgt, basis, '; '.join(labs[:8]), headl.get(path, 0)))

# ======================================================================================================
# sub-gate proposal: every file of the nine directories lands in exactly one group (first match wins)
# ======================================================================================================
import re as _re
def _p(*alts): return _re.compile('^RBM2D/(' + '|'.join(alts) + ')\\.lean$')
GROUPS = [
 ('none (class d: merged or unreachable)', lambda p, c: c == 'd'),
 ('MD vocabulary (split table, section MD)', _p('Defs/(Model|StochDom)', 'Gauss/(Model|Domination|MomentBridge|LinearForm|Envelope|SteinMatrix)',
        'Path/(PerTime|Walk|Transfer|Markov|Stop|Azuma|Step2Props)', 'Hierarchy/(Loops|Operations|OperationsPairWord)')),
 ('ST-1 Gaussian calculus, loop algebra, Step 1 (lem_GbEXP, lem_ConArg)', _p('Gauss/.*', 'Green/.*', 'Hierarchy/.*', 'Induction/(Continuity|ConArg|ConArgDet|Step1)')),
 ('ST-2 path layer and Step 2 (grid, stopping, one-step expansion, d>=3 argument)', _p('Path/.*', 'Induction/(Grid.*|AzumaProxyN|StepDecompN|LoopC2N|LoopGenN|QVN|Step2TargetV3|StoppedEndDefs)')),
 ('ST-3 Steps 3-4 (alternating/non-alternating, Q-process, (+,+) base)', _p('Induction/(?!(MainInd|Defs))[A-Za-z0-9]*')),
 ('ST-5 Step 6 (expected 2-loop, ML:exp)', _p('Evolution/(Step61|MLExp.*)')),
 ('ST-4 Step 5 (CLT, lem:sum_decay, lem_dec_calE inputs)', _p('Evolution/.*')),
 ('ST-6 assembly (lem:main_ind chain, ML:*, endpoints MR:*)', _p('Induction/(MainInd|Defs)', 'Main/(?!BUniv).*')),
 ('UN bulk universality (Thm: B_Univ)', _p('Universality/.*', 'Main/BUniv.*')),
]
def group_of(path, cl):
    for name, pred in GROUPS:
        if callable(pred):
            if pred(path, cl): return name
        elif pred.match(path): return name
    return None

def groups_table():
    agg = collections.OrderedDict((n, [0, 0, collections.Counter(), 0]) for n, _ in GROUPS)
    for (p, n, cl, tgt, basis, labs, kept) in rows:
        g = group_of(p, cl)
        assert g is not None, p
        agg[g][0] += 1; agg[g][1] += n; agg[g][2][cl] += 1; agg[g][3] += max(kept, 0)
    return agg

ST_ORDER = ['MD vocabulary (split table, section MD)',
 'ST-1 Gaussian calculus, loop algebra, Step 1 (lem_GbEXP, lem_ConArg)',
 'ST-2 path layer and Step 2 (grid, stopping, one-step expansion, d>=3 argument)',
 'ST-3 Steps 3-4 (alternating/non-alternating, Q-process, (+,+) base)',
 'ST-4 Step 5 (CLT, lem:sum_decay, lem_dec_calE inputs)',
 'ST-5 Step 6 (expected 2-loop, ML:exp)',
 'ST-6 assembly (lem:main_ind chain, ML:*, endpoints MR:*)',
 'UN bulk universality (Thm: B_Univ)',
 'none (class d: merged, unreachable or deleted by T2274)']
ST_ORDER[-1] = [n for n, _ in GROUPS if n.startswith('none')][0]

def summary_lines():
    agg = collections.defaultdict(collections.Counter); lines = collections.defaultdict(collections.Counter); kept = collections.defaultdict(int)
    for (p, n, cl, tgt, basis, labs, k) in rows:
        d = p.split('/')[1]; agg[d][cl] += 1; lines[d][cl] += n; kept[d] += max(k, 0)
    out = ['| RBM2D dir -> RBM3D dir | files | lines c9a24cf | lines kept 0c1330a | files a/b/c/d | lines a/b/c/d |', '|---|---|---|---|---|---|']
    tot = collections.Counter(); totl = collections.Counter(); tk = 0
    for d in TARGET_DIR:
        a = agg[d]; l = lines[d]
        out.append(f'| {d} -> {TARGET_DIR[d]} | {sum(a.values())} | {sum(l.values())} | {kept[d]} | {a["a"]}/{a["b"]}/{a["c"]}/{a["d"]} | {l["a"]}/{l["b"]}/{l["c"]}/{l["d"]} |')
        tot.update(a); totl.update(l); tk += kept[d]
    out.append(f'| TOTAL | {sum(tot.values())} | {sum(totl.values())} | {tk} | {tot["a"]}/{tot["b"]}/{tot["c"]}/{tot["d"]} | {totl["a"]}/{totl["b"]}/{totl["c"]}/{totl["d"]} |')
    return out

def groups_lines():
    agg = groups_table()
    out = ['| sub-gate (proposal, dependency order) | files | lines c9a24cf | lines kept 0c1330a | files a/b/c/d |', '|---|---|---|---|---|']
    for g in ST_ORDER:
        nf, nl, cc, nk = agg[g]
        out.append(f'| {g} | {nf} | {nl} | {nk} | {cc["a"]}/{cc["b"]}/{cc["c"]}/{cc["d"]} |')
    out.append(f'| TOTAL | {sum(v[0] for v in agg.values())} | {sum(v[1] for v in agg.values())} | {sum(v[3] for v in agg.values())} | |')
    return out

def dirlevel_lines():
    tot = collections.OrderedDict()
    for l in open('closure.tsv'):
        p, n, r, i = l.rstrip('\n').split('\t'); parts = p.split('/')
        d = parts[1] if len(parts) > 2 else '(root files)'
        if d in TARGET_DIR: continue
        t = tot.setdefault(d, [0, 0, 0, 0, 0]); t[0] += 1; t[1] += int(n); t[2] += int(r); t[3] += int(n) * int(r); t[4] += max(headl.get(p, 0), 0)
    tgt = {'Loop': 'RBM3D/Loop (T2004: K-loops, KBound, SumZero, Ward, TreeRep, PureLoop)', 'Propagator': 'RBM3D/Propagator + RBM3D/Kernel (T2003: Theta decay, Combes-Thomas, cutoff, symbol)',
           'Analysis': 'none needed: no file is reachable from the endpoints', 'Test': 'RBM3D/Test (axiom audit; not ported)', '(root files)': 'RBM3D/{Basic,Delocalization,Endpoints}.lean (T2001 freeze)'}
    out = ['| RBM2D dir (directory level only) | covered by | files | lines c9a24cf | lines kept 0c1330a | files reachable from the endpoints | lines reachable |', '|---|---|---|---|---|---|---|']
    for d, (nf, nl, nr, nlr, nk) in tot.items():
        out.append(f'| {d} | {tgt.get(d, "")} | {nf} | {nl} | {nk} | {nr} | {nlr} |')
    return out

MD_TICKETS = [
 ('MD-1', 'RBM3D/Defs/Sizes.lean, RBM3D/Gauss/FineModel.lean', 'Idx, blk, split(Equiv), Iblk, card_Iblk, card_Idx, zdistInf, Sizes (lam), size, WO, Bandwidth, Admissible, locDomain, withLam, W<->N conversions; svarF (svarF_eq_svar), gvarF, PF, Xentry, Xmat, Xlinear, coordinateMatrix, Hflow, seqP, slice, seqXmat, seqHflow, seqP_map_slice, E abs(X)^2 = S',
  ['Defs/Model', 'Gauss/Model', 'Gauss/LinearForm'], 'probe sections 1-4', 'none', 'prover-max (interface, every ST/UN ticket consumes it)'),
 ('MD-2', 'RBM3D/Defs/StochDomAt.lean, RBM3D/Gauss/DominationAt.lean', 'badSetAt, StochDomAt (+ calculus: refl, trans, add, mul, of_forall_le, of_unifDetDom; stochDom_iff_at_id), HighProbAt (+ inter, biInter; highProb_iff_at_id), PerTimeDomAt (+ grid union bound), Prec, PrecPT, Whp (+ prec_of_le, precPT_of_le); moment => domination and back, envelope, countable-product Stein',
  ['Defs/StochDom', 'Path/PerTime', 'Gauss/Domination', 'Gauss/MomentBridge', 'Gauss/Envelope', 'Gauss/SteinMatrix'], 'probe section 7', 'MD-1', 'prover-hard'),
 ('MD-3', 'RBM3D/Loop/GLoopFlow.lean, RBM3D/Gauss/BlockAnderson.lean', 'Gres, Mres, loopM, blockMat, loopFine, loopOf/loopL, Gt, Gn, Lloop, cutGlue (+ gloop_cutGlueL_split, gloop_cutGlueR_split), envelope (5.2) for arbitrary Hermitian H, zztE (Gt_lemT), PsiI, seqHflowBA, seqHBA, Gt_BA (m(z) = integral is T2005, merged)',
  ['Hierarchy/Loops', 'Hierarchy/Operations', 'Hierarchy/OperationsPairWord', 'Path/Step2Props'], 'probe sections 5-6', 'MD-1', 'prover-max (interface: loops and flow data)'),
 ('MD-4', 'RBM3D/Path/Walk.lean', 'PathOmega, pathP, filt, gridStep, gridTime, pathH (+ pathH_isHermitian), PrecGrid (+ precGrid_of_le); proofs of TransferLaw, IndepIncr; per-time transfer grid <-> single time',
  ['Path/Walk', 'Path/Transfer'], 'probe section 8', 'MD-1, MD-2', 'prover-hard'),
 ('MD-5', 'RBM3D/Path/Markov.lean, RBM3D/Path/Stop.lean, RBM3D/Path/Azuma.lean', 'grid Markov property and freezing, grid stopping times, Azuma-Hoeffding + Doob (replace BDG, DECISIONS §7)',
  ['Path/Markov', 'Path/Stop', 'Path/Azuma'], '-', 'MD-4', 'prover (generic, class a)'),
]

def probe_section_lines():
    import re
    t = open('/Users/junyin/Lean_proof/RBM3D-wt/T2002/RBM3D/Probe/T2002Vocab.lean').read().split('\n')
    marks = [(i, int(m.group(1))) for i, l in enumerate(t) for m in [re.match(r'^/-! ## (\d+)\.', l)] if m]
    out = {}
    for k, (i, num) in enumerate(marks):
        j = marks[k + 1][0] if k + 1 < len(marks) else len(t)
        out[num] = j - i
    return out

def md_split_lines():
    byp = {p: (n, k) for (p, n, cl, tgt, basis, labs, k) in rows}
    ps = probe_section_lines()
    out = ['| ticket | files under RBM3D/ | statements | RBM2D sources | lines c9a24cf | lines kept 0c1330a | probe lines | est. lines | depends on | role |', '|---|---|---|---|---|---|---|---|---|---|']
    for (tid, files, stm, srcs, probe, dep, role) in MD_TICKETS:
        n = sum(byp[f'RBM2D/{s}.lean'][0] for s in srcs); k = sum(max(byp[f'RBM2D/{s}.lean'][1], 0) for s in srcs)
        secs = [int(x) for x in re.findall(r'\d+', probe)] if probe[0].isdigit() or probe.startswith('probe') else []
        if 'sections' in probe:
            a, b = [int(x) for x in re.findall(r'\d+', probe)]; secs = list(range(a, b + 1))
        elif 'section' in probe:
            secs = [int(re.findall(r'\d+', probe)[0])]
        pl = sum(ps.get(x, 0) for x in secs)
        out.append(f'| {tid} | {files} | {stm} | {", ".join(srcs)} | {n} | {k} | {pl} | {k + pl} | {dep} | {role} |')
    tn = sum(sum(byp[f"RBM2D/{s}.lean"][0] for s in t[3]) for t in MD_TICKETS); tk = sum(sum(max(byp[f"RBM2D/{s}.lean"][1], 0) for s in t[3]) for t in MD_TICKETS)
    out.append(f'| total | | | | {tn} | {tk} | | | | |')
    return out

import re
KEPT = '0c1330a'
def md(path):
    import subprocess
    L = []
    A = L.append
    now = subprocess.run(['date', '-u'], capture_output=True, text=True).stdout.strip()
    head = subprocess.run(['git', '-C', '/Users/junyin/Lean_proof/RBM2D', '--no-optional-locks', 'log', '-1', '--format=%h'], capture_output=True, text=True).stdout.strip()
    A('# T2002 port map: RBM2D `c9a24cf` -> RBM3D, stochastic side (design report, ticket T2002)')
    A('')
    subj = subprocess.run(['git', '-C', '/Users/junyin/Lean_proof/RBM2D', '--no-optional-locks', 'log', '-1', '--format=%s', '99d6fe0'], capture_output=True, text=True).stdout.strip()
    shst = subprocess.run(['git', '-C', '/Users/junyin/Lean_proof/RBM2D', '--no-optional-locks', 'diff', '--shortstat', 'c9a24cf', head, '--', 'RBM2D', 'RBM2D.lean'], capture_output=True, text=True).stdout.strip()
    nlean = subprocess.run(['git', '-C', '/Users/junyin/Lean_proof/RBM2D', '--no-optional-locks', 'diff', '--stat', KEPT, head, '--', 'RBM2D', 'RBM2D.lean'], capture_output=True, text=True).stdout.strip()
    same = 'its Lean tree equals that of `' + KEPT + '`' if not nlean else 'its Lean tree differs from that of `' + KEPT + '`'
    A(f'Generated {now} by the scripts of part J. RBM2D is read at commit `c9a24cf` (the ticket\'s commit). RBM2D `HEAD` was `{head}` at generation time ({same}); commit `99d6fe0` ("{subj}") is RBM2D\'s own dead-code deletion, `git diff --shortstat c9a24cf {KEPT} -- RBM2D RBM2D.lean`: {shst}. The column "kept" is the line count at `{KEPT}` (`-1` = file deleted), i.e. the part of each file that the final d=2 proof uses.')
    mm = open('outputs/mainmoved.txt').read().split('\n')
    t5 = [l.split(' ')[0] for l in mm if re.match(r'^[0-9a-f]{7} T2005: merge', l)]
    A(f'RBM3D is read at the branch point `3c11d7b` of `main` (the tree of `t/T2002`); `main` has since moved to `{open("main_hash.txt").read().strip()}`, and the only Lean changes are the new file `RBM3D/Defs/SemicircleIntegral.lean` of T2005 (`{t5[0] if t5 else "?"}`; one public theorem, no definition: prove report b.7) and its import line in `RBM3D.lean`, so the inventory of definitions A.1 is unchanged. Line counts are `wc -l` of `git show <commit>:<file>`; "reachable" is the transitive `import` closure of `RBM2D/Main/Endpoints.lean` and `RBM2D/Main/BUnivHolds.lean` at `c9a24cf`.')
    A('')
    A('## A. Inventories (ticket item 1)')
    A('')
    A('### A.1 RBM3D on `main` (`3c11d7b`): every public definition of `Defs/*`, `Gauss/*`, `Loop/GLoop.lean`, `Analysis/Resolvent.lean`, elaborated signature (script `Inv.lean`, output verbatim, `module:line kind name : type`)')
    A('')
    A('```')
    for l in open('inv3d.out'):
        A(l.rstrip('\n'))
    A('```')
    A('')
    A('### A.2 RBM2D `c9a24cf`: the vocabulary files (script `inv.py --sig 150`, output verbatim; first line of each block = `file<TAB>lines<TAB>#public defs<TAB>#public theorems`)')
    A('')
    A('```')
    for l in open('inv2d_full.out'):
        A(l.rstrip('\n'))
    A('```')
    A('')
    A('## B. Classes and rules')
    A('')
    A('* (a) dimension-free: copy with the renaming rules R1-R4 of the prove report (no exponent token in the file; every port still re-checks each statement against this paper, CLAUDE.md §5.2);')
    A('* (b) generalize `Z2 L -> Zd d L`, `W^2 -> W^d`, `(W L)^2 -> (W L)^d`, `S^(B)` with `g = lam n`, redo the exponents (file has an exponent token, or uses the d=2 scales `scaleM`, `ellT`, `tailT`, `Meta`, `ellz`);')
    A('* (c) d=2-specific argument, replaced by the d>=3 argument named in the labels column (hand list: Step 2, Step 6, the d=2 scales, `Kstab2`); the ST design ticket of that step confirms the list;')
    A('* (d) not needed: not in the import closure of the five endpoint theorems, deleted by RBM2D T2274 as dead code, or already in merged RBM3D (target column names the merged file).')
    A('')
    A('Token rule (script `stats.py`): exponent tokens are `W ^ 2`, `L ^ 2`, `(W * L) ^ 2`, `size ^ 2`, `W⁻²`, `L²`, `d = 2`, `Z_L^2`, `5⁻¹`; the (a)/(b) split is by this rule only, so a (b) row may need less work and an (a) row more.')
    A('Labels are the labels cited in the file that also exist in the TeX of this paper (`labels.py`: `label@file:line`); (c) rows carry the replacement labels.')
    A('')
    A('## C. One row per RBM2D file (nine directories)')
    cur = None
    for (p, n, cl, tgt, basis, labs, kept) in rows:
        d = p.split('/')[1]
        if d != cur:
            cur = d
            A('')
            A(f'### {d} -> {TARGET_DIR[d]}')
            A('')
            A('| RBM2D file | lines c9a24cf | kept 0c1330a | class | RBM3D target | basis | labels (this paper) |')
            A('|---|---|---|---|---|---|---|')
        A(f'| {p.split("/", 2)[2]} | {n} | {kept} | {cl} | {tgt} | {basis} | {labs} |')
    A('')
    A('## D. Directory-level rows')
    A('')
    L.extend(dirlevel_lines())
    A('')
    A('## E. Summaries')
    A('')
    L.extend(summary_lines())
    A('')
    L.extend(groups_lines())
    A('')
    A('## E.2 Split table of the MD vocabulary tickets (computed from the rows above and the probe sections)')
    A('')
    L.extend(md_split_lines())
    A('')
    NEW = [
     ('Step 2 of d>=3 (no RBM2D source for the argument; DECISIONS §7)', ['eq:def2_stopping', 'Gronwall_inequality', 'eq:Gronwall_dervJuD', 'defCALJ', 'awi2iks', 'lem:newKLK', 'lem: EMn2_N', 'ygdhmsgq0']),
     ('light-weight term and graph expansions (sec. 7, App. B; no sister project has them, DECISIONS §2 item 3)', ['lem:LWterm', 'lem: EWGn2_N', 'lem:LWterm_EXP', 'lem:LW_moment', 'lem:LW_moment_exp', 'lem:Anp', 'lem:Anp_key', 'claim:TTk', 'def scaling order', 'Owx', 'Oe2x']),
     ('Steps 3-5 regimes that d=2 does not have (1-s <= g^2/L^2 and g^2/L^d <= 1-t <= g^2/L^2)', ['sec:1-s<L-2', 'def;zero_mode_remove', 'lem: newPQ', 'lem:STOeq_Qt_nonzero', 'lem:sum_decay_nonzero', 'lem;CLT']),
     ('block Anderson: deterministic layer and the changes of Steps 1-2 (sec. 8)', ['zztE_BA', 'lem:main_ind_BA', 'lem:propM', 'lem_GbEXP_BA', 'lem_ConArg_BA', 'self_m', 'def_G0']),
     ('propagator in d dimensions (T2003)', ['lem_propTH', 'def_Theta', 'prop:ThfadC', 'prop:BD1']),
    ]
    A('## E.3 New work with no RBM2D counterpart (paper labels of this paper, checked against `texlabels.tsv`; a label not found is printed as `?`)')
    A('')
    for title, labs in NEW:
        A(f'* {title}: ' + ', '.join(f"{x}@{short.get(texpos[x].split(':')[0], texpos[x].split(':')[0])}:{texpos[x].split(':')[1]}" if x in texpos else f'{x}?' for x in labs))
    A('')
    A('## F. `#print axioms` of every declaration printed by the probe (verbatim output of `lake env lean RBM3D/Probe/T2002Vocab.lean`; command and exit code: prove report b.1)')
    A('')
    A('```')
    for l in open('outputs/probe_raw.txt'):
        A(l.rstrip('\n'))
    A('```')
    A('')
    A('## G. The pins of the probe (script `Pins.lean`, elaborated types, output verbatim; the probe is `RBM3D/Probe/T2002Vocab.lean` on branch `t/T2002`)')
    A('')
    A('```')
    for l in open('pins_defs.out'):
        A(l.rstrip('\n'))
    A('```')
    A('')
    A('## H. The compiled instances of the probe (script `Pins.lean` in `thms` mode, namespace `RBM.Gauss.T2002Inst`, output verbatim)')
    A('')
    A('```')
    for l in open('pins_thms.out'):
        A(l.rstrip('\n'))
    A('```')
    A('')
    A('## I. Mathlib names used by the probe (script `Names.lean`: `#check`, output verbatim, continuation lines joined)')
    A('')
    A('```')
    for l in open('names.out'):
        A(l.rstrip('\n'))
    A('```')
    A('')
    A('## J. Scripts (verbatim; run in this order: `closure.py > closure.tsv`, `labels.py > texlabels.tsv`, `stats.py > stats.tsv`, `headlines.py <commit> > headlines.tsv`; `final_run.py` (every command whose output the reports paste, with `Inv.lean`, `Pins.lean`, `Pins_thms.lean` = `Pins.lean` with the last line `#pins thms RBM.Gauss.T2002Inst`, `Names.lean`, `Clash.lean` under `lake env lean`), `final_extra.py`, `postproc.py`, `mkportmap.py md <out>`, `mkreport3.py`; `inv.py` as in A.2, `invcompact.py` for the compact inventory)')
    for name in ['inv.py', 'invcompact.py', 'closure.py', 'labels.py', 'stats.py', 'headlines.py', 'final_run.py', 'final_extra.py', 'postproc.py', 'mkportmap.py', 'mkreport3.py', 'Inv.lean', 'Pins.lean', 'Names.lean', 'Deprec.lean', 'Clash.lean']:
        A('')
        A(f'### J.{name}')
        A('')
        A('```')
        for l in open(name).read().rstrip('\n').split('\n'):
            A(l)
        A('```')
    open(path, 'w').write('\n'.join(L) + '\n')

mode = sys.argv[1] if len(sys.argv) > 1 else 'rows'
if mode == 'rows':
    for r in rows: print('|'.join([''] + [str(x) for x in r] + ['']))
elif mode == 'summary': print('\n'.join(summary_lines()))
elif mode == 'groups': print('\n'.join(groups_lines()))
elif mode == 'dirlevel': print('\n'.join(dirlevel_lines()))
elif mode == 'split': print('\n'.join(md_split_lines()))
elif mode == 'md': md(sys.argv[2])
```

### J.mkreport3.py

```
#!/usr/bin/env python3
"""Compose (a'), (b)-(d) of docs/reports/T2002-prove.md from the saved script outputs (outputs/*.txt, *.out).
Section (a) (the lines before `## (a′)` / `## (b)` of the existing file) is kept verbatim.
Run after final_run.py, final_extra.py and postproc.py."""
import re, subprocess, os, sys
SC = os.path.dirname(os.path.abspath(__file__))
MAIN = '/Users/junyin/Lean_proof/RBM3D'
WT = '/Users/junyin/Lean_proof/RBM3D-wt/T2002'
REPORT = MAIN + '/docs/reports/T2002-prove.md'
OUTFILE = sys.argv[1] if len(sys.argv) > 1 else REPORT

def run(cmd, cwd=SC):
    return subprocess.run(cmd, cwd=cwd, shell=True, capture_output=True, text=True, executable='/bin/zsh').stdout

def out_of(name):          # saved output: (date, command, body lines, exit line)
    t = open(f'{SC}/outputs/{name}.txt').read().split('\n')
    while t and t[-1] == '': t.pop()
    return t[0], t[1][2:], t[2:-1], t[-1]

H = open(f'{SC}/main_hash.txt').read().strip()
now = run('date -u').strip()
base = open(REPORT).read().split('\n')
cut_at = next((i for i, l in enumerate(base) if l.startswith('## (a′)') or l.startswith('## (b)')), None)
a_part = base[:cut_at] if cut_at is not None else base
while a_part and a_part[-1] == '': a_part.pop()
assert a_part[0].startswith('Prover model:'), a_part[0]

SECS = {}
L = []
A = L.append
def sec(name):
    global L, A
    L = SECS.setdefault(name, [])
    A = L.append
sec('ap')
names_out = ['head', 'build', 'probe', 'hygiene', 'clash_import', 'pins_defs', 'pins_thms', 'names', 'inv3d', 'rbm2d',
             'mergeduse', 'mainmoved', 'locsc', 'pins_central', 'inst_central', 'hardc', 'apcorr', 'latt', 'deprec']
times = [out_of(n)[0] for n in names_out]

# ---------------------------------------------------------------- (a')
sec('ap')
da, ca, ba_, _ = out_of('apcorr')
A('')
A(f'## (a′) Preflight corrections — {now}')
A('One correction in (i); no verdict changes. The row "`(lam^2 W^d)^{-1}` (small parameter in `B_{t0,0}`, `Eq:Gtlp_exp`)": `Eq:Gtlp_exp` (1_2:1211) carries `(\\ilambda^2 W^d)^{-1/5}`; `(\\ilambda^2 W^d)^{-1}` is the quantity of `(eq:BetaK)` (1_2:514) and bounds the first term of `W^{-d}B_{t,0}` (`eq_B_param`, 1_2:1108). The row\'s bound `(lam^2 W^d)^{-1} <= W^{-2𝔡}` (hence `(lam^2 W^d)^{-1/5} <= W^{-2𝔡/5}`) and all verdicts stand.')
A('```')
A(f'$ {ca}')
L += [x[:200] for x in ba_]
A('```')

# ---------------------------------------------------------------- (b) header
sec('bh')
A('')
A(f'## (b) Script output (commands run {min(times)} .. {max(times)}; composed {now}; worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2002`, branch `t/T2002`)')
A('Blocks are pasted by the generator; `cut`/`sed`/`grep` in a command is applied to the output shown; the scratch-directory paths of the commands are shortened; every command is in portmap part J (`final_run.py`, `final_extra.py`). Full signatures (item 1), one row per RBM2D file (item 4), all pins, all instances and the scripts: `docs/reports/T2002-portmap.md` (parts A, C, G, H, J). Probe: `RBM3D/Probe/T2002Vocab.lean`.')
A('')
sec('c0')
A('### b.8 The hard constraints of item 2 and the pins that meet them (the auditor checks each against the probe; instances not shown in b.3: portmap H)')
A('| constraint | met by |')
A('|---|---|')
A('| `d` a parameter, `3 ≤ d` only where needed; `N = (WL)^d`; block size `W^d` | `Sizes d`, `Sizes.size`, `Sizes.card_Idx` (`#Idx = size`), `card_Iblk` (`#block = W^d`); the grep below finds `3 ≤ d` nowhere and `0 < d` only in `W_rpow_le`; instances at `d = 3` |')
A('| `λ` a sequence with `(eq:WO)`, never fixed | field `Sizes.lam : ℕ → ℝ`, `Sizes.WO`, `Sizes.Admissible`; instances `sz0_admissible`, `sz0_lam_tendsto` (`lam → 0`), `sz0_lam_sq` |')
A('| energies are `E : ℕ → ℝ` | `Sizes.LocalLawPT (E t : ℕ → ℝ)`, instance `localLaw_sz0` along the non-constant `Eseq n = 1/(n+2)`; `Gt_prec`, `Gt_whp`, `gridRes_prec`, `Gt_timeIcc_prec` also use `Eseq`; matrix-level `Gt`, `Lloop`, `Gn` take one `E` (TEAM §8 lesson 23) |')
A('| one scale for every `≺`; conversion of `W^τ` | `Prec`, `PrecPT`, `PrecGrid`, `Whp`, `LocalLawPT` all at `sz.size`; merged `StochDom` is `StochDomAt id` (`stochDom_iff_at_id`); `W_rpow_le`, `size_rpow_le_W_rpow`; instances `W_le_size_sz0`, `size_le_W_sz0` |')
A('| names: `d` is the dimension | `sz : Sizes d` (rule R1 in b.9); new public names and clashes: b.1 |')
A('| block Anderson fits or gets a layer | same vocabulary: `seqHflowBA`, `seqHBA`, `PsiI`, `Mres`; `Gt_BA` compiled; the deterministic layer is separate (b.9) |')
dh, ch, bh, _ = out_of('hardc')
A('```')
A(f'$ {ch}'); L += bh
A('```')

# ---------------------------------------------------------------- b.1
sec('b1')
A('### b.1 Build, axioms (every printed declaration: portmap part F), hygiene, name clash')
d, cmd, body, ex = out_of('head')
d2, cmd2, body2, ex2 = out_of('build')
A('```')
A(f'$ {cmd}'); L += [x[:190] for x in body]
A(f'$ lake build RBM3D.Probe.T2002Vocab 2>&1 | grep -v "depends on axioms" | tail -3'); L += body2
d, cmd, body, ex = out_of('probe')
A('$ lake env lean RBM3D/Probe/T2002Vocab.lean > probe_raw.txt 2>&1; echo "exit=$?"; wc -l < probe_raw.txt; grep -c "<S>" probe_raw.txt; grep -vc "<S>" probe_raw.txt; tail -2 probe_raw.txt   # <S> = depends on axioms: [propext, Classical.choice, Quot.sound]')
L += body
d, cmd, body, ex = out_of('hygiene')
A('$ grep -nE "sorry|admit|native_decide|^axiom " RBM3D/Probe/T2002Vocab.lean; echo "grep exit=$?"; wc -l RBM3D/Probe/T2002Vocab.lean'); L += body
d, cmd, body, ex = out_of('clash_import')
pins = [l for l in open(f'{SC}/pins_defs.out')]
thms = [l for l in open(f'{SC}/pins_thms.out')]
names = []
for l in pins:
    m = re.match(r'^T2002Vocab\.lean:\d+ (\S+) (\S+) : ', l)
    if m and 'T2002Inst' not in m.group(2): names.append(m.group(2))
# theorems of the probe outside T2002Inst are public names as well
sub = subprocess.run(['grep', '-nE', r'^theorem [A-Za-z_0-9.]+', f'{WT}/RBM3D/Probe/T2002Vocab.lean'], capture_output=True, text=True).stdout.split('\n')
thm_names = []
ns_stack = []
for ln in open(f'{WT}/RBM3D/Probe/T2002Vocab.lean').read().split('\n'):
    m = re.match(r'^theorem\s+([^\s:(\[{]+)', ln)
    if m: thm_names.append(m.group(1))
shorts = sorted(set([n.split('.')[-1] for n in names] + [n.split('.')[-1] for n in thm_names]))
hits_wt, hits_main = [], []
for short in shorts:
    pat = r'(def|theorem|abbrev|structure|instance|class|inductive|lemma)[[:space:]]+(noncomputable[[:space:]]+)?' + re.escape(short) + r'([^A-Za-z0-9_]|$)'
    r = subprocess.run(['grep', '-rnE', pat, 'RBM3D', '--include=*.lean', '--exclude-dir=Probe'], cwd=WT, capture_output=True, text=True)
    hits_wt += [(short, x) for x in r.stdout.strip().split('\n') if x]
    r = subprocess.run(['git', 'grep', '-nE', pat, H, '--', 'RBM3D'], cwd=MAIN, capture_output=True, text=True)
    hits_main += [(short, x) for x in r.stdout.strip().split('\n') if x]
A('$ lake env lean Clash.lean   # import RBM3D and import RBM3D.Probe.T2002Vocab together (worktree = 3c11d7b): a clash would be a Lean error'); L += body
A(f'$ for each short name N of the {len(shorts)} public pins and lemmas of the probe (T2002Inst excluded): grep -rnE "(def|theorem|abbrev|structure|instance|class|inductive|lemma) N" RBM3D --exclude-dir=Probe   # in the worktree and by git grep in main {H}')
A(f'same short name declared elsewhere in the worktree: {len(hits_wt)}; in main {H}: {len(hits_main)}')
for s_, h in hits_wt[:4] + hits_main[:4]: A(f'  {s_}: {h[:140]}')
A('```')

# ---------------------------------------------------------------- b.2 pins
sec('b2')
dpc, cpc, bpc, _ = out_of('pins_central')
npins = len([l for l in pins if l.strip()])
A(f'### b.2 Central pins (statements extracted by script from the compiled probe, elaborated types; all {npins} pin lines: portmap part G)')
A('```')
A(f'$ lake env lean Pins.lean | sed ... | grep -E "^[0-9]+ (def|structure) RBM\\.(Gauss\\.|Path\\.)?(<central names>) :" | sed ... | cut -c1-205   # exact command: portmap part J, final_run.py, step pins_central; {len(bpc)} lines')
L += bpc
A('```')

# ---------------------------------------------------------------- b.3 instances
sec('b3')
dic, cic, bic, _ = out_of('inst_central')
nthm = len([l for l in thms if l.strip()])
A('### b.3 Compiled nonempty instances at the preflight sequence (`d = 3`, `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`; `n = 0`: `L=4, W=32, lam=1/64, N=2097152`; `𝔠 = 1/6`, `𝔡 = 1/10`, `κ = ε = 1/10`)')
A('```')
A(f'$ lake env lean Pins_thms.lean | sed ... | grep -E "^[0-9]+ theorem RBM\\.Gauss\\.T2002Inst\\.(<central names>) :" | sed ... | cut -c1-215   # exact command: portmap part J, final_run.py, step inst_central; {len(bic)} of {nthm} instance statements; every deterministic hypothesis of the applied pins is discharged; `TransferLaw`, `IndepIncr` (MD-4 targets) stay hypotheses of `transfer_at`, `indep_at`; `lam0`, `m0`, `hzt` (MA gate) of `Gt_BA_sz0`')
L += bic
A('```')

# ---------------------------------------------------------------- b.4 inventory
sec('b4')
inv_raw = run('python3 invcompact.py').rstrip('\n').split('\n')
r3 = [x for x in inv_raw if x.split(':')[0] in ('Defs', 'Gauss', 'Loop', 'Analysis')]
r2 = [x.split(' | ')[0] for x in inv_raw if x.startswith('RBM2D/')]
cnt3 = '; '.join(re.match(r'^(\w+): (\d+) files, (\d+) lines, (\d+) defs', x).expand(r'\1 \2 files \3 lines \4 defs') for x in r3 if re.match(r'^(\w+): (\d+) files', x))
inv = ['RBM3D (main 3c11d7b, public definitions): ' + cnt3, 'RBM2D c9a24cf (file: lines, public defs): ' + '; '.join(r2)]
A('### b.4 Inventory (item 1; full signatures in portmap part A)')
A('```')
A('$ python3 invcompact.py   # RBM3D from Inv.lean (tree of `t/T2002` = main 3c11d7b), RBM2D from inv.py at c9a24cf; names and signatures: portmap A.1, A.2')
L += inv
A('```')

# ---------------------------------------------------------------- b.5 decisions
sec('dec')
A('### b.9 Decisions, one row per object (keep = merged RBM3D, port = RBM2D `c9a24cf`, bridge = both)')
A('')
rows = [
 ('Index type, blocks', '**bridge both**: fine lattice `Idx d L W = Zd d (W*L)` carries the model and the statements (port RBM2D `Idx`); block-product `Vtx d L W = Zd d L × Fin (W^d)` (keep) carries `E_a`, `S`, loops; bridges `splitEquiv`, `blockMat`, `svarF_eq_svar`', '`(G_bound)` is at `x,y ∈ Z_{WL}^d` with `|x-y|` (1_2:262-275, 388-389); RBM2D\'s chain: `blockMat` in {nbm} files (b.7); probe `Idx, split(Equiv), Iblk`, `card_Iblk = W^d`, `Sizes.card_Idx`'),
 ('Distance `\\|x\\|`', '**keep both**: `zdistD` (l1, merged, propagator side); new `zdistInf` (L^inf) for stochastic and endpoint statements', 'paper fixes L^inf (1_2:274); merged `Defs/Lattice.lean:14-15` fixes l1 (b.7); `zdistInf ≤ zdistD ≤ d·zdistInf` compiled; T2002b'),
 ('Size sequence, `λ`', '**port + extend**: `Sizes d {L W lam three_le_L W_pos}`, `size n = (W n·L n)^d`, `WO`, `Bandwidth`, `SizeTendsto`, `Admissible 𝔠 𝔡`, `withLam`; `lam : ℕ → ℝ` unconstrained except `WO`', 'RBM2D `Sizes` (Gauss/Model.lean:405) has no coupling; `lam` = paper\'s `\\ilambda` (macro for `g`, `main.tex:199`) = the `g` of merged `SB, ellT, Bparam`'),
 ('Probability space, model', '**port**: one countable product `seqP sz` over `Σ n, CoordF d (L n) (W n)`; one-size law `PF`; merged `Gauss.P` (Vtx, finite `Measure.pi`, fixed sizes) kept, not used outside `Gauss/Model.lean` (b.7)', '`StochDom` needs one probability space while merged `Gauss.P` has one per size (RBM3D DECISIONS §10 T2001i-k); RBM2D has the same `seqP` (`Gauss/Model.lean:434`); `seqP_map_slice` compiled; `S` from merged `SBR` (`svarF_eq_svar`)'),
 ('`H`, flow `H_t`, path carrier', '**port**: `Xmat`, `seqXmat sz n ω`; single time `seqHflow sz n u ω = √u • seqXmat` (the definition here; RBM2D has `Hflow` at `Gauss/Model.lean:327` and `seqHflow_eq_smul` = `rfl` at `:499`); grid walk `PathΩ, pathP, filt, gridStep, gridTime, pathH` with pins `TransferLaw`, `IndepIncr`; stopping times only where the paper stops (`Sol_CalL`, `lem:DIfREP`, `eq:def2_stopping`); Azuma+Doob replace BDG', 'DECISIONS §7; (bandcw0) 1_2:296, (MBM) 1_2:686; merged `Hmat` kept; the single-time law makes `zztE` pointwise (`Gt_lemT`)'),
 ('`m`, `z_t`, `η_t`', '**keep + bridge**: merged `mE`, `msc`, `lemE`, `lemT`, `zt`, `Gauss.etaT`; generic `ztOf m E t`, `etaOf m t` (`zt_eq_ztOf` is `rfl`); `m(z)` as the integral: ported by T2005 (`msc_eq_integral`, merged after this branch point, b.7)', 'BA: `m(E, λ_0)` is data; RBM2D `Path.etaT` not ported: merged `Gauss.etaT` is the single `η_t` (RBM2D kept two equal copies, `RBM.KLoop.etaT` and `RBM.Path.etaT`, bridged by its T2042; RBM2D DECISIONS §14)'),
 ('`G_t(σ)`, `G(z)`, `E_a`', '**bridge**: generic `Gres H z σ`; `Sizes.Gt`, `Gn` (entries on `Idx`); merged `Gsig` is `Gres (Hmat ω) (zt E t)` (`Gsig_eq_Gres`, `rfl`): the time-one matrix only; `E_a`: keep merged `Gauss.Eblk` (`trace_Eblk = 1`)', '(def_Green) 1_2:336, (Eq:defGLoop) 1_2:824'),
 ('`𝓛^{(n)}_{t,σ,a}`', '**bridge**: `loopM d L W H z σ a` (`Fin`-indexed; merged `gloop` = `loopM (Hmat ω) (zt E t)`, `rfl`); `loopFine` via `blockMat`; `Sizes.Lloop`; list form `loopL`, `loopOf` ↔ merged `RBM.Loop.LoopIdx`', '`Lloop_zero_one`: `𝓛^{(1)}_{0,σ,a} = m(σ)`, i.e. `K^{(1)}` (Def_Ktza, 1_2:988)'),
 ('Hierarchy, `Def:oper_loop`', '**port, no Itô**: `cutGlue` (RBM2D `Hierarchy/Operations.lean:27`, class a); merged `cutGlueL/R`; `lem:SE_basic` replaced by the one-step expansion on the grid walk (RBM2D Path/OneStep, Expansion; b) and per-time Stein identities (b)', 'DECISIONS §7'),
 ('`≺`, scale, w.h.p.', '**port + one scale**: `StochDomAt P size`, `HighProbAt`, `PerTimeDomAt`; `Sizes.Prec`, `PrecPT`, `PrecGrid`, `Whp` all at `N = sz.size n = (W n L n)^d`; merged `StochDom`, `HighProb` are the case `size = id` (`stochDom_iff_at_id`, `highProb_iff_at_id`)', '`(stoch_domination)` itself uses `N^τ`, `N^{-D}` (1_2:229); RBM2D re-pinned its chain once (DECISIONS §214, §216); `W^τ ≤ N^{τ/d}` always and `N^τ ≤ W^{τ/𝔠}` under `W ≥ N^𝔠`, so `≺` at scale `N` ⟺ the paper\'s `W^τ` statements'),
 ('Energies', 'sequences `E : ℕ → ℝ`, `\\|E n\\| ≤ 2-κ` in every sequence-level statement (`LocalLawPT`); matrix-level objects take one real `E` (RBM2D practice)', 'TEAM §8 lesson 23'),
 ('Block Anderson', '**same vocabulary**, three differences: law `seqP (sz.withLam 0)` (`S^{(B)}(0)=I`), shift `H_0 = lam0•PsiI` (`seqHflowBA`, `seqHBA`), data `m, M` from `(self_m)`, `(def_G0)` (`Mres (lam•Ψ) z m`, `M ≠ m I`); separate layer only for the deterministic `m(z,g)`, `M^{(B)}`, `e_g` (MA gate)', '1_2:606-633; `Gt_BA` compiled; `Mres_zero_msc`: band `M = m I`'),
 ('Controls', '**keep merged** `ellT`, `Bparam`, `BparamR`, `tailT`; add `Bctl = W^{-d}B_{t,0}` as the single control; RBM2D `scaleM`, `Path.ellT` (d=2) not ported', '(Eq:L-KGt) 1_2:1196, (con_st_ind) 1_2:1296, (eq:ellt), (eq_B_param)'),
]
_rb = '\n'.join(out_of('rbm2d')[2])
nbm = re.search(r'c9a24cf: blockMat: \d+ lines in (\d+) files', _rb).group(1)
rows[0] = (rows[0][0], rows[0][1], rows[0][2].replace('{nbm}', nbm))
A('| object | decision (probe pins) | reason, paper line |')
A('|---|---|---|')
for o, dcs, rs in rows: A(f'| {o} | {dcs} | {rs} |')
A('')
A('Renaming rules for ports: **R1** `d : Sizes` → `sz : Sizes d`; the dimension `d : ℕ` is a leading explicit argument of every ported declaration that mentions `Z2`, `Idx`, `Sizes`, `W^2`, `L^2`, `(W*L)^2` (fields `sz.L n`, `sz.W n`, `sz.lam n`, `sz.size n`). **R2** `Z2 L → Zd d L`, `Idx L W → Idx d L W`, `BlockIndex L W → Vtx d L W`, `zdist2 → zdistD` (l1) or `zdistInf` (L^inf), `LoopIdx → RBM.Loop.LoopIdx`, `spectralM, spectralZ → mE, zt`, `Path.etaT → Gauss.etaT`, list `Gsig/gloop → Gres/loopL`. **R3** `W^2 → W^d`, `(W⁻¹)^2 → ((W:ℝ)^d)⁻¹`, `L^2 → L^d`, `(W*L)^2 → (W*L)^d`, five-point `S^(B)` → `S^(B)(g)` with `g := sz.lam n`, `Path.ellT L u → ellT L (sz.lam n) u`, `scaleM → (Bctl)⁻¹`. **R4** clashes with merged `RBM.Gauss.*`: `Coord → CoordF`, `svar → svarF`, `gvar → gvarF`, `P → PF`; other public names keep their RBM2D name; unpinned helpers `private` or stem-prefixed (CLAUDE.md §3 (E)).')

# ---------------------------------------------------------------- b.6 port map summary
sec('pm')
A('### b.5 Port map (item 4; one row per RBM2D file in the portmap, part C) and the sub-gates of ST')
sm = run('python3 mkportmap.py summary').rstrip('\n').split('\n')
gp = run('python3 mkportmap.py groups').rstrip('\n').split('\n')
dl = run('python3 mkportmap.py dirlevel').rstrip('\n').split('\n')[2:]
A('```')
A('$ python3 mkportmap.py summary   # classes a/b/c/d defined in portmap part B; "kept" = lines at RBM2D 0c1330a, after its own dead-code deletion T2274')
L += [x for x in sm if not x.startswith('|---')]
A('$ python3 mkportmap.py dirlevel   # directory level only (Loop: T2004, Propagator: T2003); files / lines c9a24cf / kept / files reachable from the endpoints')
A('; '.join(f"{c[0]}: {c[2]} / {c[3]} / {c[4]} / {c[5]}" for c in ([y.strip() for y in x.split('|')[1:-1]] for x in dl)))
A('$ python3 mkportmap.py groups   # sub-gates of ST in dependency order: files / lines kept at 0c1330a / files a/b/c/d (full table: portmap E)')
A('; '.join(f"{c[0].split(' ')[0]}: {c[1]} / {c[3]} / {c[4]}" for c in ([y.strip() for y in x.split('|')[1:-1]] for x in gp[2:-1])))
A('```')

# ---------------------------------------------------------------- b.7 split tables
sec('sp')
A('### b.6 Split table (MD vocabulary tickets; sizes by `python3 mkportmap.py split`) and the first ST design tickets')
sp = run('python3 mkportmap.py split').rstrip('\n').split('\n')
for x in sp[2:-1]:
    c = [y.strip() for y in x.split('|')[1:-1]]
    A(f'* **{c[0]}** (`{c[1]}`): sources {c[3]} ({c[4]} / {c[5]} lines, probe {c[6]}, est. {c[7]}); needs {c[8]}; {c[9]}.')
A('The statements of each MD ticket are the probe pins of the same sections (portmap part E.2); `Defs/SemicircleIntegral` is T2005\'s, merged. `PrecGrid` sits with the carrier (MD-4); `LocalLawPT` needs `Gt` (MD-3) and `PrecPT` (MD-2) and is the pin shape for the ST design tickets, not an MD item. First ST design tickets (after this audit; each ends in pins compiled in a probe, an exponent table with the regimes `1-t ≥ g²`, `g²/L² ≤ 1-t ≤ g²`, `g²/L^d ≤ 1-t ≤ g²/L²`, and a split table):')
g = {x.split('|')[1].strip()[:4]: [y.strip() for y in x.split('|')[1:-1]] for x in gp if x.startswith('| ST-')}
def gl(k): c = g[k]; return f'{c[1]} files / {c[3]} lines kept'
ncc2 = g['ST-2'][4].split('/')[2]
A(f'* **ST-D1** Step 1 (`lem_GbEXP`, `lem_ConArg`, 3_5:14, 42): Green, Gauss calculus, Hierarchy, Induction/{{Continuity,ConArg*,Step1}}, {gl("ST-1")}; new for d ≥ 3: exponents only (3_5:29-40 says the proofs are dimension-independent). **ST-D2** Step 2 (`Eq:Gdecay_w`, `eq:def2_stopping`, `lem:newKLK`, `lem: EMn2_N`, 3_5:302-899): Path, Induction/Grid*, {gl("ST-2")}; new: the d ≥ 3 argument ({ncc2} class-c files), written together with the light-weight design (LW).')
A(f'* **ST-D3** Steps 3-4 (`lem:STOeq_NQ`, `Def:QtPt`, `lem:iterations`, 3_5:900-1934): Induction, {gl("ST-3")}; new: the case `1-s ≤ g²/L²` (`def;zero_mode_remove`, `lem: newPQ`). Later: ST-D4 Step 5 ({gl("ST-4")}), ST-D5 Step 6 ({gl("ST-5")}), ST-D6 assembly with T2001 ({gl("ST-6")}). Order: MD-1 first (every ticket consumes it), then MD-2 and MD-3 in parallel, MD-4, MD-5; ST-D1..D3 together once MD-1 is merged; ST-D4..D6 after the ST-D2 pins.')

# ---------------------------------------------------------------- b.8 evidence
sec('ev')
dr, cr, br, _ = out_of('rbm2d')
dm, cm, bm, _ = out_of('mergeduse')
dmm, cmm, bmm, _ = out_of('mainmoved')
dl2, cl2, bl2, _ = out_of('locsc')
dlt, clt, blt, _ = out_of('latt')
A('### b.7 Evidence: RBM2D movement and usage, `main` since the branch point, the merged Vtx model, the endpoint form, the merged norm (run in `~/Lean_proof/RBM3D` resp. the worktree)')
A('```')
A(f'$ {cr[:150]} ...'); L += br
A(f'$ {cmm[:170]} ...'); L += bmm
A(f'$ {cm[:150]} ...'); L += bm
A(f'$ {cl2}'); L += bl2
A(f'$ {clt}'); L += blt
A('```')
clo = {l.split('\t')[0]: int(l.split('\t')[2]) for l in open(f'{SC}/closure.tsv')}
hd = {l.split('\t')[0]: int(l.split('\t')[1]) for l in open(f'{SC}/headlines.tsv')}
nine = {'Defs', 'Gauss', 'Green', 'Hierarchy', 'Path', 'Induction', 'Evolution', 'Main', 'Universality'}
def inn(p): parts = p.split('/'); return len(parts) > 2 and parts[1] in nine
sel = [p for p in clo if inn(p)]
unr = [p for p in sel if clo[p] == 0]; unr_del = [p for p in unr if hd[p] < 0]
rea_del = [p for p in sel if clo[p] == 1 and hd[p] < 0]
tot_files = len(sel)

# ---------------------------------------------------------------- narrative
sec('nar')
rb = [l for l in br if re.match(r'^[0-9a-f]{7} ', l)]
rhead = re.search(r'RBM2D HEAD: (\S+); lines of diff --stat 0c1330a HEAD -- RBM2D RBM2D.lean: (\d+)', '\n'.join(br))
ncommits = len(rb)
A('### Narrative (at most 40 lines)')
cls = [x for x in sm if x.startswith('| TOTAL')][0].split('|')
tot_files9, tot_lines, tot_kept, tot_fc, tot_lc = [c.strip() for c in cls[2:7]]
probe_lines = len(open(f'{WT}/RBM3D/Probe/T2002Vocab.lean').read().split('\n')) - 1
nar = f'''1. Delivered: probe `RBM3D/Probe/T2002Vocab.lean` ({probe_lines} lines; `lake build` prints "Build completed successfully" and `lake env lean` exits 0 (b.1); {npins} pin lines and {nthm} instance theorems of `T2002Inst`, central ones in b.2-b.3; axioms standard on every printed declaration), hard-constraint table (b.8), decision table (b.9), inventories (b.4, portmap A), port map of {tot_files9} RBM2D files ({tot_lines} lines at `c9a24cf`) with classes a/b/c/d = {tot_fc} (b.5, portmap C), split tables (b.6).
2. Route: RBM2D's (DECISIONS §7): one countable Gaussian product over the sizes, the single-time flow `H_u = √u X` wherever the paper uses no stopping time, the grid walk on `pathP` where it stops. The carrier is on the fine lattice `Z_{{WL}}^d`, the loops on the block-product index, bridged by `splitEquiv`; `svarF_eq_svar` and `Sizes.card_Idx` (`#Idx = N`) tie the fine-lattice model to the merged one.
3. Finding (merged code): `Gauss.Gsig`/`gloop`/`loopMax` are built on `Hmat ω`, the time-one matrix (`Gsig_eq_Gres` is `rfl`); they are not the `G_t` of a flow matrix. The generic `Gres`/`loopM` removes this and `gloop_eq_loopM` is `rfl`, so the merged envelope `norm_gloop_le` applies at the merged model (`loop_envelope`). The Vtx model (`Gauss.Model`) is used in code only by `Loop/GLoop.lean` (the other two files of the b.7 grep mention it in comments); it is kept.
4. Finding (RBM2D and main moved): RBM2D `HEAD` is `{rhead.group(1) if rhead else '?'}`, {ncommits} commits after the ticket's `c9a24cf` (b.7); `99d6fe0` is its own dead-code deletion (82 modules removed, 328 trimmed), and its Lean tree equals that of `0c1330a` (diff lines: {rhead.group(2) if rhead else '?'}). The port map keeps `c9a24cf` as ticketed and adds the kept-line column at `0c1330a`: {tot_kept} of {tot_lines} lines in the nine directories survive. Of the {tot_files} files of the nine directories, {len(unr)} are unreachable in my import closure (`closure.py`), {len(unr_del)} of them were deleted by `99d6fe0`, and {len(rea_del)} further files that my closure reaches by imports were deleted as whole-dead modules (T2274 report: 82 whole-dead modules in all). `main` is at `{H}`; T2005 added `Defs/SemicircleIntegral.lean` (`msc_eq_integral`, no definition; b.7), so the portmap lists the RBM2D file of that name as class d and MD-3 does not own it.
5. Finding (endpoint form): the paper's `(G_bound)` intersects over `z ∈ D_{{κ,ε}}` inside the probability (1_2:388-389, b.7); RBM2D's `locSC` has `∀ z` outside the probability (b.7), the inside form being the endpoint gate's duty (RBM2D DECISIONS §16, §17: `RegionUnifOfPT`), and `99d6fe0` deleted as dead code `Path/NetLift.lean` (1784 lines, lift from per time to uniform in `u`) and `Main/RegionUnif.lean` (950 lines, lift over the spectral region). With T2001b of RBM3D (DECISIONS §10: paper form) these two return (marked b in the portmap).
6. Compiled consistency checks: `Lloop_zero_one`: `𝓛^{{(1)}}_{{0,σ,a}} = m(σ)` under `E_a = W^{{-d}}1(x=y∈[a])`, `z_0 = E+m^{{(E)}}`, `tr`; `Gt_lemT`: the third clause of `(eq:zztE)` holds pointwise for `H_u = √u X` (an identity, not a coupling); `Gt_BA`: the same for the block Anderson flow given `λ_0 = √t_0 λ`, `z_{{t_0}}(E,λ_0) = √t_0 z`; `Mres_zero_msc`: band `M = m I`; `stochDom_iff_at_id`: merged `StochDom` is `StochDomAt id`.
7. Scale and `λ`: the one scale is `N = sz.size n = (W n L n)^d` (the paper's own `≺` uses `N^τ`, `N^{{-D}}`); `W_rpow_le`, `size_rpow_le_W_rpow` convert `W^τ ↔ N^τ'`; `Sizes.lam : ℕ → ℝ` is constrained only by `WO` (`lam_n → 0` in the instance). Block Anderson fits the band vocabulary (b.9); the deterministic layer (`m(z,g)`, `M^{{(B)}}`, `e_g`) supplies `m0`, `hzt`, `hlam0` of `Gt_BA`.
8. Limits: (a)/(b) is a token rule (portmap B), (c) is a hand list to be confirmed by the ST design tickets; `kept` is RBM2D's own dead-code result for the d = 2 route; no RBM2D proof was checked beyond its header and token statistics; `three_le_L` and `W_pos` are fields of `Sizes` (all `n`), not eventual conditions.'''
for l in nar.split('\n'): A(l)

# ---------------------------------------------------------------- (c)
sec('cc')
A('')
A('## (c) Verified Mathlib names used (`#check`; all names of the probe in the portmap part I)')
nm = [l.rstrip('\n') for l in open(f'{SC}/names.out')]
keep = ['finFunctionFinEquiv', 'Measure.eq_infinitePi', 'Matrix.inv_smul', 'Matrix.nonsing_inv_eq_ringInverse', 'Matrix.IsHermitian.submatrix', 'Matrix.conjTranspose_kronecker', 'Matrix.conjTranspose_sum', 'Matrix.IsHermitian.add', 'Matrix.conjTranspose_smul', 'Real.one_le_rpow', 'measure_empty']
for k in keep:
    for l in nm:
        head_ = l.split(' :')[0].lstrip('@')
        if head_.endswith(k):
            A(f'`{head_}` :{l.split(" :", 1)[1][:105]}'); break
dd, cd, bd, _ = out_of('deprec')
A('```')
A(f'$ lake env lean Deprec.lean 2>&1 | grep -o "warning: .*" | cut -c1-120   # #check @Set.mem_setOf_eq; #check @if_true; #check @ite_true; #check @Set.mem_ofPred_eq')
L += bd
A('```')

# ---------------------------------------------------------------- (d)
sec('dd')
A('')
A('## (d) Open issues and paper-delta candidates')
A(f'* **O1 port source commit**: the ticket pins RBM2D `c9a24cf`; `HEAD` `{rhead.group(1) if rhead else "?"}` has the trimmed Lean tree of `0c1330a` (b.7). The dispatcher should fix the commit that MD/ST tickets cite (CLAUDE.md §5.2), with the NetLift/RegionUnif caveat (narrative 5). **O2 endpoint form**: DECISIONS §10 (T2001b) fixes the paper\'s form (`∩_z` inside `P`), so the two lifts RBM2D deleted (`Path/NetLift.lean`, `Main/RegionUnif.lean`) are needed (class b in the portmap; MA-gate obligation); the vocabulary has `Prec` (union inside `P`) and `PrecPT` (per time).')
A(f'* **O3 Step 2**: the d ≥ 3 argument has no sister-project source (DECISIONS §7; the {ncc2} class-c files of ST-D2 are the d = 2 version to be replaced) and needs the light-weight design (§7, `lem:LWterm`, `lem: EMn2_N`) at the same time. **O4 MA gate**: `m(z,g)`, `M^{{(B)}}`, `e_g` and the clauses `λ_0 = √t_0 λ`, `z_{{t_0}}(E,λ_0) = √t_0 z` are inputs of `Gt_BA`; no probe pin proves them. **O5 merged files**: `Gauss/Model.lean` (Vtx model, finite `Measure.pi`) and the `ω`-based part of `Loop/GLoop.lean` stay; supersede only with the dead-code tool at the end (TEAM §9.13).')
A('* **T2002a** (naming): `lam` is the paper\'s `\\ilambda`, printed `g` (`main.tex:199`, `def:ilambda` 1_2:256); the text also uses `λ` for `\\ilambda^{-1}` (1_2:253). **T2002b** (norm): the paper uses L^inf (1_2:274), merged `Defs/Lattice.lean:14-15` says the norm is immaterial and fixes l1; `e^{-(|a|/ℓ)^{1/2}}` and `B_{t,|a|}` carry fixed constants, so statements use `zdistInf`. **T2002c** (necessary condition): `three_le_L` in `Sizes` (as merged `Defs/Block.lean` and RBM2D); the paper only says `L` even (1_2:269); already signed as part of T2001a (DECISIONS §10). **T2002d** (convention): `ZMod (W*L)` with zero-based blocks `[a] = a.val·W + {0..W-1}` versus the paper\'s `⟦-WL/2+1, WL/2⟧` and `⟦(a(i)-1)W+1, a(i)W⟧` (1_2:262-267): equivalent by a translation, the model reads only block labels. **T2002e** ("N sufficiently large", 1_2:366) is `∀ᶠ n` along the sequence and `N → ∞` is explicit (signed as T2001a, DECISIONS §10). **T2002f** (merged docstring): the module doc of `Loop/GLoop.lean` (line 17) writes `G_t(+) = (H_t - z_t)^{-1}`, but `Gsig` takes `Hmat ω`, the matrix `H` at time one, for every `t` (narrative 3). **T2002g** (Lean writing, route of DECISIONS §7): the flow `(MBM)` (1_2:686) is carried by the single-time law `seqHflow` and, where the paper uses stopping times, by the grid walk `pathH` on `pathP` (independent increments; BDG replaced by Azuma and Doob); all sizes live on one product space `seqP` (every size has the one-size law, `seqP_map_slice`); per-time `≺` (`PrecPT`) has the union over `u` outside `P`; the paper lifts to all `z` by an `N^{-C}`-net (1_2:1228), RBM2D by `Path/NetLift.lean` (time) and `Main/RegionUnif.lean` (spectral region) (narrative 5; MA gate, DECISIONS §10 T2001b). **T2002h** (Lean writing): `G(z) = (H - z)⁻¹` is `Ring.inverse (H - z • 1)` in `Gres` and `Mres` (a total function, equal to the inverse whenever it exists, in particular for Hermitian `H` and `Im z ≠ 0`, `isUnit_sub_smul_of_isHermitian`). **T2002i** (equivalent form): the paper\'s `(G_bound)`, `(G_bound_ave)` carry `W^τ` (1_2:388-393) while its `≺` carries `N^τ` (1_2:229); the pins use `N^τ` throughout, and under `W ≥ N^𝔠` with `W^d ≤ N` the two are equivalent (`size_rpow_le_W_rpow`, `W_rpow_le`).')

order = ['ap', 'bh', 'b1', 'b2', 'b3', 'b4', 'pm', 'sp', 'ev', 'c0', 'dec', 'nar', 'cc', 'dd']
out = a_part + [x for k in order for x in SECS[k]]
open(OUTFILE, 'w').write('\n'.join(out) + '\n')
print('lines:', len(out), '->', OUTFILE)
```

### J.Inv.lean

```
import RBM3D
open Lean Elab Command Meta

/-- Print every public (non-private, non-internal) definition / inductive / structure of the
given modules, with its elaborated type, source line and kind. -/
elab "#inventory " mods:ident* : command => do
  let env ← getEnv
  let wanted : Array Name := mods.map (·.getId)
  let mut rows : Array (Name × Nat × String × Name × ConstantInfo) := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames[idx.toNat]!
    unless wanted.contains modName do continue
    if isPrivateName n then continue
    if n.isInternal then continue
    if n.hasMacroScopes then continue
    let isDef := match ci with
      | .defnInfo _ => true
      | .inductInfo _ => true
      | .opaqueInfo _ => true
      | _ => false
    unless isDef do continue
    if env.isProjectionFn n then continue
    if isMatcherCore env n then continue
    let kind : String := match ci with
      | .defnInfo _ => if isStructure env n then "def" else "def"
      | .inductInfo _ => if isStructure env n then "structure" else "inductive"
      | _ => "opaque"
    let line ← match (← findDeclarationRanges? n) with
      | some r => pure r.range.pos.line
      | none => pure 0
    rows := rows.push (modName, line, kind, n, ci)
  let sorted := rows.qsort fun a b => if a.1 == b.1 then a.2.1 < b.2.1 else a.1.toString < b.1.toString
  for (m, line, kind, n, ci) in sorted do
    let ty ← liftTermElabM <| MetaM.run' <| withOptions (fun o => (o.setBool `pp.funBinderTypes true).setBool `pp.unicode.fun true) do
      let f ← ppExpr ci.type
      pure (toString f)
    let ty := (ty.replace "\n" " ").replace "  " " "
    logInfo m!"{m}:{line} {kind} {n} : {ty}"

#inventory RBM3D.Defs.Block RBM3D.Defs.Convolution RBM3D.Defs.Domination RBM3D.Defs.Lattice RBM3D.Defs.Neighbours RBM3D.Defs.Params RBM3D.Defs.RadialSum RBM3D.Defs.Semicircle RBM3D.Defs.Shells RBM3D.Defs.StochDom RBM3D.Defs.Tail RBM3D.Gauss.Domination RBM3D.Gauss.Envelope RBM3D.Gauss.Model RBM3D.Gauss.Stein RBM3D.Gauss.SteinMatrix RBM3D.Loop.GLoop RBM3D.Analysis.Resolvent
```

### J.Pins.lean

```
import RBM3D.Probe.T2002Vocab
open Lean Elab Command Meta

/-- Print every non-private definition / structure / instance of the module, with its elaborated
type (`kind name : type`), in source order; with `thm`, the theorems whose name has the given
prefix instead. -/
elab "#pins " mode:ident pfx:ident : command => do
  let env ← getEnv
  let wantThm := mode.getId == `thms
  let pre := pfx.getId
  let mut rows : Array (Nat × String × Name × ConstantInfo) := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    unless env.header.moduleNames[idx.toNat]! == `RBM3D.Probe.T2002Vocab do continue
    if isPrivateName n || n.isInternal || n.hasMacroScopes then continue
    if env.isProjectionFn n then continue
    if isMatcherCore env n then continue
    if isNoConfusion env n || isCasesOnRecursor env n || isAuxRecursor env n then continue
    let last := n.getString!
    if last == "ctorIdx" || last == "noConfusionType" || last == "noConfusion" || last == "recOn" || last == "casesOn" then continue
    let ok := match ci with
      | .defnInfo _ => !wantThm
      | .inductInfo _ => !wantThm
      | .thmInfo _ => wantThm && pre.isPrefixOf n
      | _ => false
    unless ok do continue
    let kind : String := match ci with
      | .inductInfo _ => if isStructure env n then "structure" else "inductive"
      | .thmInfo _ => "theorem"
      | _ => "def"
    let line ← match (← findDeclarationRanges? n) with
      | some r => pure r.range.pos.line
      | none => pure 0
    rows := rows.push (line, kind, n, ci)
  let sorted := rows.qsort fun a b => a.1 < b.1
  for (line, kind, n, ci) in sorted do
    let ty ← liftTermElabM <| MetaM.run' <| withOptions (fun o => (o.setBool `pp.funBinderTypes true).setBool `pp.unicode.fun true) do
      let f ← ppExpr ci.type
      pure (toString f)
    let ty := (ty.replace "\n" " ").replace "  " " "
    logInfo m!"T2002Vocab.lean:{line} {kind} {n} : {ty}"

#pins defs RBM
```

### J.Names.lean

```
import RBM3D.Probe.T2002Vocab
#check @finFunctionFinEquiv
#check @MeasureTheory.Measure.infinitePi
#check @MeasureTheory.Measure.eq_infinitePi
#check @MeasureTheory.Measure.infinitePi_pi
#check @ProbabilityTheory.gaussianReal
#check @MeasureTheory.Filtration.piLE
#check @Matrix.inv_smul
#check @Matrix.nonsing_inv_eq_ringInverse
#check @Matrix.inv_eq_right_inv
#check @Matrix.isUnit_iff_isUnit_det
#check @Matrix.IsHermitian.submatrix
#check @Matrix.conjTranspose_kronecker
#check @Matrix.trace_diagonal
#check @Real.pow_rpow_inv_natCast
#check @Real.rpow_le_rpow_of_exponent_le
#check @Real.rpow_le_one_of_one_le_of_nonpos
#check @Filter.Tendsto.inv_tendsto_atTop
#check @Nat.le_self_pow
#check @Fintype.bijective_iff_injective_and_card
#check @Finset.card_equiv
#check @ZMod.val_natCast_of_lt
#check @smul_mul_smul_comm
#check @Set.mem_ofPred_eq
#check @Matrix.conjTranspose_sum
#check @Matrix.IsHermitian.add
#check @Matrix.conjTranspose_smul
#check @Real.one_le_rpow
#check @MeasureTheory.measure_empty
```

### J.Deprec.lean

```
import RBM3D.Probe.T2002Vocab
#check @Set.mem_setOf_eq
#check @if_true
#check @ite_true
#check @Set.mem_ofPred_eq
```

### J.Clash.lean

```
import RBM3D
import RBM3D.Probe.T2002Vocab
-- compiles iff no declaration of the probe has the same full name as a declaration of the library
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let n := env.constants.fold (init := 0) fun acc nm _ =>
    match env.getModuleIdxFor? nm with
    | some i => if env.header.moduleNames[i.toNat]! == `RBM3D.Probe.T2002Vocab then acc + 1 else acc
    | none => acc
  IO.println s!"import RBM3D + RBM3D.Probe.T2002Vocab: ok; constants of the probe module: {n}"
```
