# T2001 coverage table (dependency table of the survey)

Produced by the scripts reproduced in the appendix (TeX scan, declaration index of RBM3D `main` and of RBM2D `c9a24cf`, hand mapping rendered by `render.py`).
Sources: paper TeX `paper/tex/*.tex` (comments stripped before scanning); RBM3D Lean at worktree `t/T2001` = `main` `3c11d7b` (`RBM3D/` before the probe); RBM2D snapshot `git -C ../RBM2D --no-optional-locks archive c9a24cf RBM2D`.

**Class** (of the Lean statement against the paper statement, signatures only; docstrings are not evidence, CLAUDE.md 5.7, 5.10): `i` proved as stated, no extra hypotheses; `ii` proved only conditionally (unproved hypotheses / Prop parameters listed); `iii` special case only (restriction named); `iv` absent (no declaration on main states it; declarations listed in the Lean column are ingredients or Prop placeholders, said so in the note).  A row split into parts `#..` has one class per part.  **Scope**: `band` the Lean/paper statement is for the random band model only, `BA` block Anderson only, `both`.  **Gate**: the gate of `docs/ROUTES.md` that owns the row (`F0 MD PT KL EK ST LW MA UN BA`; `-` for remarks/examples).  **Consumers**: rows or section pseudo-nodes (`[sec file:line title]`, `[StepN-proof ..]`) whose statement or proof text cites a label of the row (script, nearest enclosing row or section; at most 6 shown).  **§5 source**: the row region cites one of the items of DECISIONS 5 (script: `\cite` keys in the region of the row) or the hand note names it; such rows are internal by DECISIONS 5.

## Summary (script)

- rows: 172 (TeX rows 170 + pseudo rows 2); classes: i=17, ii=3, iii=18, iv=134
- per gate (i/ii/iii/iv): - 0/0/0/4; BA 0/0/1/20; EK 5/0/2/1; F0 10/0/2/2; KL 0/3/4/7; LW 0/0/2/26; MA 0/0/1/10; MD 2/0/6/6; PT 0/0/0/5; ST 0/0/0/51; UN 0/0/0/2
- rows with a gate (excluding 4 remark/example rows and 2 pseudo rows): 166; label literally named in `docs/ROUTES.md`: 48; not literally named: 118 (by gate: ST 46, LW 20, BA 16, MA 10, F0 8, MD 6, EK 6, KL 5, UN 1)

## Part A: result rows (one row per line)

| # | row (paper label) | labels in row | TeX file:line | kind | gate | scope | class | Lean on main: file:line `signature` (script-extracted) | restriction / unproved hypotheses / note | consumers (script) | RBM2D analogue at c9a24cf (file:line `declaration`) | §5 source |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | `stoch_domination` | stoch_domination | 1_2:229 | eq/def | MD | both | i | Defs/StochDom.lean:80 `def StochDom (ξ ζ : ∀ N, U N → Ω → ℝ) : Prop` ⟦#check: `{Ω : Type u_1} → [inst : MeasurableSpace Ω] → MeasureTheory.Measure Ω → {U : ℕ → Type u_2} → ((N : ℕ) → U N → Ω → ℝ) → ((N : ℕ) → U N → Ω → ℝ) → Prop`⟧<br>Defs/StochDom.lean:85 `def NormStochDom {E : Type*} [Norm E] (A : ∀ N, U N → Ω → E) (ζ : ∀ N, U N → Ω → ℝ) : Prop` ⟦#check: `{Ω : Type u_1} → [inst : MeasurableSpace Ω] → MeasureTheory.Measure Ω → {U : ℕ → Type u_2} → {E : Type u_3} → [Norm E] → ((N : ℕ) → U N → Ω → E) → ((N : ℕ) → U N → Ω → ℝ) → Prop`⟧<br>Defs/StochDom.lean:89 `def HighProb (Ξ : ℕ → Set Ω) : Prop` ⟦#check: `{Ω : Type u_1} → [inst : MeasurableSpace Ω] → MeasureTheory.Measure Ω → (ℕ → Set Ω) → Prop`⟧<br>Defs/StochDom.lean:93 `def HighProbIn (Ξ Ω' : ℕ → Set Ω) : Prop` ⟦#check: `{Ω : Type u_1} → [inst : MeasurableSpace Ω] → MeasureTheory.Measure Ω → (ℕ → Set Ω) → (ℕ → Set Ω) → Prop`⟧<br>Defs/Domination.lean:57 `def DetDom (f g : ℕ → ℝ) : Prop` ⟦#check: `(ℕ → ℝ) → (ℕ → ℝ) → Prop`⟧<br>Defs/Domination.lean:52 `def UnifDetDom {U : ℕ → Type*} (f g : ∀ N, U N → ℝ) : Prop` ⟦#check: `{U : ℕ → Type u_1} → ((N : ℕ) → U N → ℝ) → ((N : ℕ) → U N → ℝ) → Prop`⟧ | defs as in the paper; convention: ONE fixed (Omega,P) with N-indexed families, while Gauss.P is one law per (d,L,W,g): no common space for a size sequence on main | [sub 1_2:1188 Proof of the main results], Eq:Gtlp_exp_flow | Defs/StochDom.lean:91 `StochDom`<br>Defs/StochDom.lean:118 `HighProb`<br>Defs/Domination.lean:56 `DetDom`<br>Defs/Domination.lean:51 `UnifDetDom` |  |
| 2 | `def:ilambda` | def:ilambda | 1_2:256 | eq/def | F0 | both | i | Defs/Block.lean:44 `noncomputable def SB : Matrix (Zd d L) (Zd d L) ℂ` ⟦#check: `(d L : ℕ) → ℝ → Matrix (RBM.Zd d L) (RBM.Zd d L) ℂ`⟧ | g := lambda^{-1} is the parameter g of SB/Gauss.svar; lambda of the ticket = \ilambda = g (paper main.tex:199) | eq:variancematrix, eq:H_blocka | none (d=2 has no coupling parameter: g=1) |  |
| 3 | `eq:blockIa` | eq:blockIa | 1_2:266 | eq/def | MD | both | iii | Gauss/Model.lean:60 `abbrev Vtx : Type` ⟦#check: `ℕ → ℕ → ℕ → Type`⟧ | Vtx = Zd d L x Fin(W^d): block label and position; no fine-lattice geometry, so \|x-y\| of (G_bound) has no meaning on Vtx (probe uses W\|[x]-[y]\|) | MR:locSC, def: BM2 | Defs/Model.lean:143 `Iblk` |  |
| 4 | `representativeL` | representativeL | 1_2:273 | eq/def | F0 | both | iii | Defs/Lattice.lean:63 `abbrev Zd (d L : ℕ) : Type` ⟦#check: `ℕ → ℕ → Type`⟧<br>Defs/Lattice.lean:71 `def zdistD (d L : ℕ) (x : Zd d L) : ℕ` ⟦#check: `(d L : ℕ) → RBM.Zd d L → ℕ`⟧ | block lattice only; periodic l^1 distance (paper-delta D2) instead of l^infinity; fine lattice Z_{WL}^d absent | (none cited; statement/definition) | Defs/Block.lean:41 `Z2`<br>Defs/Dist.lean:30 `zdist` |  |
| 5 | `bandcw0` | bandcw0 | 1_2:295 | eq/def | MD | band | iii | Gauss/Model.lean:112 `noncomputable def Hmat (ω : Omega d L W) : Matrix (Vtx d L W) (Vtx d L W) ℂ` ⟦#check: `(d L W : ℕ) → [NeZero L] → RBM.Gauss.Omega d L W → Matrix (RBM.Gauss.Vtx d L W) (RBM.Gauss.Vtx d L W) ℂ`⟧<br>Gauss/Model.lean:101 `noncomputable def P : Measure (Omega d L W)` ⟦#check: `(d L W : ℕ) → ℝ → [NeZero L] → MeasureTheory.Measure (RBM.Gauss.Omega d L W)`⟧<br>Gauss/Model.lean:94 `noncomputable def gvar (c : Coord d L W) : ℝ≥0` ⟦#check: `(d L W : ℕ) → ℝ → RBM.Gauss.Coord d L W → NNReal`⟧<br>Gauss/Model.lean:119 `theorem Hmat_isHermitian (ω : Omega d L W) : (Hmat d L W ω).IsHermitian`<br>Gauss/Model.lean:162 `theorem P_map_update (c : Coord d L W) : ((P d L W g).prod (gaussianReal 0 (gvar d L W g c))).map (upd c) = P d L W g` | variance profile fixed to S(g); one law per (d,L,W,g): no size sequence, no common space, no time t (H_t absent) | [sub 1_2:599 Main results for the block Anderso] | Gauss/Model.lean:155 `Gauss.Xmat`<br>Gauss/Model.lean:127 `Gauss.P`<br>Gauss/Model.lean:405 `Gauss.Sizes`<br>Gauss/Model.lean:434 `Gauss.Sizes.seqP` |  |
| 6 | `eq:variancematrix` | eq:variancematrix | 1_2:303 | eq/def | F0 | band | i | Defs/Block.lean:44 `noncomputable def SB : Matrix (Zd d L) (Zd d L) ℂ` ⟦#check: `(d L : ℕ) → ℝ → Matrix (RBM.Zd d L) (RBM.Zd d L) ℂ`⟧<br>Propagator/Props4.lean:48 `noncomputable def SBR : Matrix (Zd d L) (Zd d L) ℝ` ⟦#check: `(d L : ℕ) → ℝ → Matrix (RBM.Zd d L) (RBM.Zd d L) ℝ`⟧<br>Gauss/Model.lean:63 `noncomputable def svar (x y : Vtx d L W) : ℝ` ⟦#check: `(d L W : ℕ) → ℝ → RBM.Gauss.Vtx d L W → RBM.Gauss.Vtx d L W → ℝ`⟧<br>Defs/Block.lean:136 `theorem norm_SB (hL : 3 ≤ L) : ‖SB d L g‖ = 1`<br>Defs/Block.lean:113 `theorem SB_mulVec_one (hL : 3 ≤ L) : SB d L g *ᵥ (1 : Zd d L → ℂ) = 1` | 3 <= L is explicit (D1) for double stochasticity; g a real number per size (a sequence needs the T2002 structure) | def:Theta, bandcwV, MBM, def_flow, lem:SE_basic, def_Theta …(+2) | Defs/Block.lean:56 `SB`<br>Defs/Model.lean:35 `Svar`<br>Gauss/Model.lean:42 `Gauss.svar` | internal by DECISIONS §5: [YY_25]@1_2:309; [DYYY25]@1_2:309; other cited keys in the row region (outside the DECISIONS §2 inventory): [Wigner]@1_2:330 |
| 7 | `def_Green` | def_Green | 1_2:335 | eq/def | MD | both | iii | Loop/GLoop.lean:87 `noncomputable def Gsig (ω : Omega d L W) (E t : ℝ) (σ : Bool) : Matrix (Vtx d L W) (Vtx d L W) ℂ` ⟦#check: `(d L W : ℕ) → [NeZero L] → RBM.Gauss.Omega d L W → ℝ → ℝ → Bool → Matrix (RBM.Gauss.Vtx d L W) (RBM.Gauss.Vtx d L W) ℂ`⟧ | only G_t(sigma) at z_t of the flow for the time-1 matrix Hmat; the resolvent at a general z is not defined on main | MR:decol, MR:locSC, eq:Psi3D, MR:decol_BA | Delocalization.lean:42 `green` |  |
| 8 | `eq:defmzsc#root` | eq:defmzsc | 1_2:339 | eq/def | F0 | both | i | Defs/Semicircle.lean:116 `noncomputable def msc (z : ℂ) : ℂ` ⟦#check: `ℂ → ℂ`⟧<br>Defs/Semicircle.lean:118 `theorem msc_mul (z : ℂ) : msc z * (msc z + z) = -1`<br>Defs/Semicircle.lean:123 `theorem msc_im_pos {z : ℂ} (hz : 0 < z.im) : 0 < (msc z).im`<br>Defs/Semicircle.lean:152 `theorem norm_msc_lt_one {z : ℂ} (hz : 0 < z.im) : ‖msc z‖ < 1` | root form with Im m > 0 (branch by Classical.choose) | [sec 1_2:1 Introduction], MR:locSC, def:Theta, def_flow | Defs/Semicircle.lean:42 `msc` |  |
| 9 | `eq:defmzsc#integral` | eq:defmzsc | 1_2:339 | eq/def | F0 | both | iv | none | integral form of the Stieltjes transform absent (needed for the pin: probe defines mSC by the integral) | [sec 1_2:1 Introduction], MR:locSC, def:Theta, def_flow | Defs/SemicircleIntegral.lean:187 `msc_eq_integral`<br>Endpoints.lean:252 `Endpoints.mSC_eq_msc` |  |
| 10 | `eq:defMzsc` | eq:defMzsc | 1_2:343 | eq/def | MD | band | iv | none | M = m I_N (matrix) absent; probe uses Mband | MR:locSC, def_flow | none (scalar mSC z used) |  |
| 11 | `MR:decol` | MR:decol, Main_DEL_COND, eq:WO, eq:psikLinfty | 1_2:357 | theorem [Delocalization] | MA | band | iv | none | endpoint 1; nothing on main states or uses it | MR:locSC, eq:ukx, MR:QUE, Thm: B_Univ, MR:QuDiff, MR:decol_BA …(+4) | Endpoints.lean:88 `Endpoints.decol`<br>Main/DecolFromLocal.lean:239 `Endpoints.decol_of_locSC`<br>Main/Endpoints.lean:36 `Endpoints.decol_holds` | other cited keys in the row region (outside the DECISIONS §2 inventory): [Aizenman1993]@1_2:373, [PelSchShaSod]@1_2:373 |
| 12 | `eq:spectral_domain` | eq:spectral_domain | 1_2:380 | eq/def | MA | band | iv | none | domain D_{kappa,eps} absent | zztE | Endpoints.lean:74 `Endpoints.locDomain` |  |
| 13 | `eq:calBetaK` | eq:calBetaK | 1_2:384 | eq/def | MA | both | iv | Defs/Params.lean:36 `noncomputable def Bparam (d L : ℕ) (g t : ℝ) (K : ℕ) : ℝ` ⟦#check: `ℕ → ℕ → ℝ → ℝ → ℕ → ℝ`⟧ | calB_{eta,K} absent; B_{t,K} (Bparam) is the t-version, related by (eq:BtBt) which is absent | defi:ofB | Defs/Semicircle.lean:298 `Meta` |  |
| 14 | `MR:locSC` | MR:locSC, G_bound, G_bound_ave | 1_2:386 | theorem [Local semicircle law] | MA | band | iv | none | endpoint 2 (G_bound, G_bound_ave) | MR:decol, Thm: B_Univ, MR:QuDiff, MR:decol_BA, [sub 1_2:681 Stochastic flow and loop hierarchy], [sub 1_2:1188 Proof of the main results] …(+4) | Endpoints.lean:99 `Endpoints.locSC`<br>Main/Endpoints.lean:30 `Endpoints.locSC_holds` |  |
| 15 | `eq:ukx` | eq:ukx | 1_2:399 | eq/def | MA | both | iv | Analysis/Resolvent.lean:110 `theorem norm_sub_smul_ge_of_isHermitian {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ} (hH : H.IsHermitian) (z : ℂ) (v : EuclideanSpace ℂ n) : \|z.im\| * ‖v‖ ≤ ‖Matrix.toEuclideanLin H v - z • v‖` | \|psi_k(x)\|^2 <= eta Im G_xx(lambda_k+i eta) absent; main has only \|\|(H-z)^{-1}\|\| <= 1/\|Im z\| (Analysis/Resolvent) | MR:decol | Main/DecolFromLocal.lean:97 `Endpoints.DecolFromLocal_sq_le_two_mul_im_green` |  |
| 16 | `MR:QUE` | MR:QUE, eq:defIE, Meq:QUE, Meq:QUE2 | 1_2:406 | theorem [Quantum unique ergodicity] | MA | band | iv | none | endpoint 3 (Meq:QUE, Meq:QUE2) | eq:ukx, Thm: B_Univ, eq:BetaK, MR:decol_BA, lem: EMn2_N | Endpoints.lean:145 `Endpoints.QUE`<br>Main/QUEFromQDiff.lean:1048 `Endpoints.QUE_of_QDiff`<br>Main/Endpoints.lean:39 `Endpoints.QUE_holds` | internal by DECISIONS §5: [Xu:2024aa]@1_2:444; [YY_25]@1_2:521; [DYYY25]@1_2:521; [RBSO1D]@1_2:521 |
| 17 | `Thm: B_Univ` | Thm: B_Univ, eq:universality | 1_2:452 | theorem [Bulk universality] | UN | band | iv | none | endpoint 4; external input LSY Thm 2.2 only (DECISIONS 5) | MR:decol_BA, lem: EMn2_N | Endpoints.lean:209 `Endpoints.BUniv`<br>Main/BUnivHolds.lean:32 `Endpoints.bUniv_holds`<br>Universality/UnivMain.lean:449 `Univ.univMainRow` | internal by DECISIONS §5: [YY_25]@1_2:470; [DYYY25]@1_2:470; [RBSO1D]@1_2:470; [Xu:2024aa]@1_2:568; other cited keys in the row region (outside the DECISIONS §2 inventory): [erdHos2025zigzag]@1_2:470 |
| 18 | `def:Theta` | def:Theta | 1_2:472 | eq/def | F0 | band | i | Propagator/Basic.lean:70 `noncomputable def Theta (ξ : ℂ) : Matrix (Zd d L) (Zd d L) ℂ` ⟦#check: `(d L : ℕ) → [NeZero L] → ℝ → ℂ → Matrix (RBM.Zd d L) (RBM.Zd d L) ℂ`⟧ | Theta^{(+,-)}(z)=Theta d L g (\|m\|^2), Theta^{(+,+)}(z)=Theta d L g (m^2); Ring.inverse(1 - xi S^(B)) | MR:decol_BA, def_Theta, [sub 7_8:105 Graphical tools and local expansio] | Propagator/Basic.lean:83 `Theta` |  |
| 19 | `MR:QuDiff` | MR:QuDiff, eq:diffu1, eq:diffu2, Meq:QdS1, Meq:QdS2 | 1_2:488 | theorem [Quantum diffusion] | MA | band | iv | none | endpoint 5 (diffu1, diffu2, Meq:QdS1, Meq:QdS2) | MR:locSC, MR:QUE, eq:BetaK, MR:decol_BA, [sub 1_2:681 Stochastic flow and loop hierarchy], [sub 1_2:1188 Proof of the main results] …(+1) | Endpoints.lean:173 `Endpoints.QDiff`<br>Main/Endpoints.lean:33 `Endpoints.QDiff_holds` |  |
| 20 | `eq:BetaK` | eq:BetaK | 1_2:514 | eq/def | MA | both | iv | none | calB_{eta,K} ~ (N eta)^{-1} >= (g^2 W^d)^{-1} for eta <= g^2/L^d: elementary, absent | MR:QUE | none (d=2 Meta has no K) |  |
| 21 | `ssfa2` | ssfa2 | 1_2:524 | eq/def | MA | band | iv | none | QUE from QD: spectral decomposition + Markov (proof step) | MR:QUE | Main/QUEFromQDiff.lean:1048 `Endpoints.QUE_of_QDiff` |  |
| 22 | `ssfa2_deter` | ssfa2_deter | 1_2:531 | eq/def | MA | band | iv | none | QUE from QD: deterministic bound (proof step) | MR:QUE | Main/QUEFromQDiff.lean:1048 `Endpoints.QUE_of_QDiff` |  |
| 23 | `bandcwV` | bandcwV | 1_2:605 | eq/def | BA | BA | iv | Gauss/Model.lean:101 `noncomputable def P : Measure (Omega d L W)` ⟦#check: `(d L W : ℕ) → ℝ → [NeZero L] → MeasureTheory.Measure (RBM.Gauss.Omega d L W)`⟧ | V is Gauss.P d L W 0 (S^(B)(0)=I) but nothing names it; no BA model on main | MR:decol_BA, MBM, def_flow, lem:LW_moment, lem:LW_moment_exp | none |  |
| 24 | `eq:H_blocka` | eq:H_blocka | 1_2:610 | eq/def | BA | BA | iv | none | H = V + g Psi absent | lem_GbEXP | none |  |
| 25 | `eq:Psi3D` | eq:Psi3D | 1_2:614 | eq/def | BA | BA | iv | Defs/Lattice.lean:108 `def Adj (d L : ℕ) (x y : Zd d L) : Prop` ⟦#check: `(d L : ℕ) → RBM.Zd d L → RBM.Zd d L → Prop`⟧ | Psi = Psi^(B) (x) I_{W^d} absent (Adj is the neighbour relation) | lem:LWterm, lem: EWGn2_N, lem:LW_moment, lem:LW_moment_exp, lem:propM, def_atom | none | internal by DECISIONS §5: [Biane]@1_2:624 |
| 26 | `self_m` | self_m | 1_2:626 | eq/def | BA | BA | iv | none | self-consistent equation for m(z,g), free convolution with semicircle: absent | eq:defmzsc, MR:decol_BA, def_flow, lem:main_ind_BA | Universality/FreeConv.lean:636 `Univ.freeConv_existsUnique`<br>Universality/FreeConv.lean:673 `Univ.isFreeConv32_unique` — different object (free convolution of OU flow), existence+uniqueness of the subordination equation | internal by DECISIONS §5: [Biane] (1_2:624, density of the free convolution) |
| 27 | `def_G0` | def_G0 | 1_2:631 | eq/def | BA | BA | iv | none | M(z)=(g Psi - z - m)^{-1}, M^(B) absent | eq:defmzsc, MR:decol_BA, def_flow, def_Theta, lem:main_ind_BA | none | internal by DECISIONS §5: [LeeSchSteYau2015]@1_2:634; other cited keys in the row region (outside the DECISIONS §2 inventory): [knowles2017anisotropic]@1_2:634, [He2018]@1_2:634, [AEK_PTRF]@1_2:634, [EKS_Forum]@1_2:634 |
| 28 | `MR:decol_BA` | MR:decol_BA, def:Theta_BA | 1_2:644 | theorem [Main results for the block A] | BA | BA | iv | none | endpoint 6 (4 bullets); needs self_m, def_G0, e_g, def:Theta_BA | def_Theta, [sub 1_2:1188 Proof of the main results], lem:LWterm, lem: EWGn2_N, [sec 7_8:1792 Extension to the block Anderson mo], lem:main_ind_BA | none | other cited keys in the row region (outside the DECISIONS §2 inventory): [PelSchShaSod]@1_2:672 |
| 29 | `MBM` | MBM | 1_2:685 | eq/def | MD | both | iv | none | matrix Brownian motion H_t absent; main has the time-1 matrix only (Gauss.Hmat) and the resampling identity P_map_update | (none cited; statement/definition) | Gauss/Model.lean:495 `Gauss.Sizes.seqHflow`<br>Path/Walk.lean:44 `Path.PathΩ`<br>Path/Walk.lean:47 `Path.pathP` | other cited keys in the row region (outside the DECISIONS §2 inventory): [10.1214/19-ECP278]@1_2:692, [Sooster2019]@1_2:692, [DY]@1_2:692 |
| 30 | `def_flow` | def_flow, eq:zt, eta, self_Gt | 1_2:714 | definition [Flow framework] | MD | band | iii | Defs/Semicircle.lean:179 `noncomputable def zt (E t : ℝ) : ℂ` ⟦#check: `ℝ → ℝ → ℂ`⟧<br>Defs/Semicircle.lean:38 `noncomputable def mE (E : ℝ) : ℂ` ⟦#check: `ℝ → ℂ`⟧<br>Loop/GLoop.lean:70 `noncomputable def etaT : ℝ` ⟦#check: `ℝ → ℝ → ℝ`⟧<br>Loop/GLoop.lean:74 `theorem etaT_eq_zt_im : etaT E t = (zt E t).im`<br>Loop/GLoop.lean:87 `noncomputable def Gsig (ω : Omega d L W) (E t : ℝ) (σ : Bool) : Matrix (Vtx d L W) (Vtx d L W) ℂ` ⟦#check: `(d L W : ℕ) → [NeZero L] → RBM.Gauss.Omega d L W → ℝ → ℝ → Bool → Matrix (RBM.Gauss.Vtx d L W) (RBM.Gauss.Vtx d L W) ℂ`⟧ | z_t, eta_t on main (band, m(E,g)=m(E)); H_t and G_{t;E,g} absent: Gsig uses the time-1 Hmat (variance S, not tS) | [sec 1_2:1 Introduction], zztE, lem_WI_K, defi:ofB, lem_ConArg, lem:newKLK …(+2) | Gauss/Model.lean:495 `Gauss.Sizes.seqHflow`<br>Gauss/SpectralWindow.lean:34 `Gauss.spectralZ`<br>Path/Scales.lean:38 `Path.etaT` |  |
| 31 | `def_G0t` | def_G0t, eq:opS | 1_2:736 | remark | MD | both | iv | none | matrix Dyson equation for M_t and M_t(z_t)=M absent | (none cited; statement/definition) | none (scalar m only) |  |
| 32 | `eq:opS` | eq:opS | 1_2:749 | sub-label/eq | MD | both | iv | none | covariance operator S[X] absent | (none cited; statement/definition) | none |  |
| 33 | `zztE#alg` | zztE, eq:t0E0, eq:zztE | 1_2:787 | lemma [Lemma 2.8 of citeYY25] | MD | band | i | Defs/Semicircle.lean:190 `noncomputable def lemE (z : ℂ) : ℝ` ⟦#check: `ℂ → ℝ`⟧<br>Defs/Semicircle.lean:193 `noncomputable def lemT (z : ℂ) : ℝ` ⟦#check: `ℂ → ℝ`⟧<br>Defs/Semicircle.lean:264 `theorem msc_eq_sqrt_mul_mE : msc z = (Real.sqrt (lemT z) : ℂ) * mE (lemE z)`<br>Defs/Semicircle.lean:270 `theorem eq_inv_sqrt_mul_zt : z = (Real.sqrt (lemT z) : ℂ)⁻¹ * zt (lemE z) (lemT z)`<br>Defs/Semicircle.lean:256 `theorem lemT_eq : (lemT z : ℂ) = msc z ^ 2 / mE (lemE z) ^ 2`<br>Defs/Semicircle.lean:359 `theorem lemma28_quant {κ : ℝ} (hκ0 : 0 < κ) (hz0 : 0 < z.im) (hz1 : z.im ≤ 1) (hκ : \|z.re\| ≤ 2 - κ) : \|lemE z\| ≤ 2 - κ ∧ (1 / 16 : ℝ) ≤ lemT z ∧ (1 / 16 : ℝ) * z.im ≤ (zt (lemE z) (lemT z)).im ∧ (zt (lemE z) (lemT z)).im ≤ (1 / 16 : ℝ)⁻¹ * z.im` | first two identities of (eq:zztE) and the range bounds (t0=lemT, E=lemE); the Im-form t0 = Im m/(Im m + Im z) of (eq:t0E0) is not stated (derivable from msc_add_eq_neg_inv) | MR:locSC, MR:QuDiff, def_Theta, ML:GLoop, lem:main_ind, lem_ConArg | Defs/Semicircle.lean:272 `zztE_quant`<br>Defs/Semicircle.lean:179 `msc_eq_sqrt_mul_spectralM` | internal by DECISIONS §5: Lemma 2.8 of [YY_25] |
| 34 | `zztE#law` | zztE, eq:t0E0, eq:zztE | 1_2:787 | lemma [Lemma 2.8 of citeYY25] | MD | band | iv | none | G(z) =_d sqrt(t0) G_{t0;E} (equality in law) absent: needs H_t ~ sqrt(t) H | MR:locSC, MR:QuDiff, def_Theta, ML:GLoop, lem:main_ind, lem_ConArg | Gauss/Model.lean:495 `Gauss.Sizes.seqHflow`<br>Path/Transfer.lean:58 `Path.gridTransferPT` | internal by DECISIONS §5: Lemma 2.8 of [YY_25] |
| 35 | `Def:G_loop` | Def:G_loop, Eq:defGLoop, def_mtzk, Eq:defwtG | 1_2:811 | definition [G-loop] | MD | band | iii | Loop/GLoop.lean:50 `noncomputable def Eblk (a : Zd d L) : Matrix (Vtx d L W) (Vtx d L W) ℂ` ⟦#check: `(d L W : ℕ) → RBM.Zd d L → Matrix (RBM.Gauss.Vtx d L W) (RBM.Gauss.Vtx d L W) ℂ`⟧<br>Loop/GLoop.lean:87 `noncomputable def Gsig (ω : Omega d L W) (E t : ℝ) (σ : Bool) : Matrix (Vtx d L W) (Vtx d L W) ℂ` ⟦#check: `(d L W : ℕ) → [NeZero L] → RBM.Gauss.Omega d L W → ℝ → ℝ → Bool → Matrix (RBM.Gauss.Vtx d L W) (RBM.Gauss.Vtx d L W) ℂ`⟧<br>Loop/GLoop.lean:92 `noncomputable def gloop (ω : Omega d L W) (E t : ℝ) {n : ℕ} (σ : Fin n → Bool) (a : Fin n → Zd d L) : ℂ` ⟦#check: `(d L W : ℕ) → [NeZero L] → RBM.Gauss.Omega d L W → ℝ → ℝ → {n : ℕ} → (Fin n → Bool) → (Fin n → RBM.Zd d L) → ℂ`⟧<br>Loop/GLoop.lean:70 `noncomputable def etaT : ℝ` ⟦#check: `ℝ → ℝ → ℝ`⟧<br>Loop/GLoop.lean:97 `noncomputable def loopMax (ω : Omega d L W) (E t : ℝ) (n : ℕ) : ℝ` ⟦#check: `(d L W : ℕ) → [NeZero L] → RBM.Gauss.Omega d L W → ℝ → ℝ → ℕ → ℝ`⟧ | loop of the time-1 matrix at z_t, NOT L_t (not equal in law); centered resolvent Gc_t = G_t - M absent | Def:oper_loop, ML:GtLocal | Hierarchy/Loops.lean:92 `gloop`<br>Gauss/Model.lean:495 `Gauss.Sizes.seqHflow` | internal by DECISIONS §5: [YY_25]@1_2:841; [DYYY25]@1_2:841 |
| 36 | `Def:oper_loop` | Def:oper_loop | 1_2:905 | definition | MD | both | iii | Loop/TreeRep.lean:84 `def cutGlueL (k l : ℕ) (b : α) (x : LoopIdx α) : LoopIdx α` ⟦#check: `{α : Type u_1} → ℕ → ℕ → α → RBM.Loop.LoopIdx α → RBM.Loop.LoopIdx α`⟧<br>Loop/TreeRep.lean:89 `def cutGlueR (k l : ℕ) (b : α) (x : LoopIdx α) : LoopIdx α` ⟦#check: `{α : Type u_1} → ℕ → ℕ → α → RBM.Loop.LoopIdx α → RBM.Loop.LoopIdx α`⟧ | index-level cutL/cutR only; the single-edge cut^{(a)}_k is not defined | (none cited; statement/definition) | Hierarchy/Operations.lean:27 `LoopIdx.cutGlue`<br>Hierarchy/OperationsPair.lean:23 `LoopIdx.cutGlueL`<br>Hierarchy/OperationsPair.lean:28 `LoopIdx.cutGlueR` | internal by DECISIONS §5: [YY_25] Lemma 2.11 of@1_2:946 |
| 37 | `lem:SE_basic` | lem:SE_basic, eq:mainStoflow, def_Edif, def_EwtG | 1_2:949 | lemma [Loop hierarchy] | MD | band | iv | none | loop hierarchy (Ito): RBM2D proves the expected ODE (Stein) and the pathwise grid identity, not Ito | [sec 1_2:1 Introduction], [sec 3_5:1 Steps 1 and 2: A priori G-loop est], [sub 3_5:69 Dynamics of (cal L-cal K)-loops], DefKsimLK, Sol_CalL, [Step2-proof: 3_5:302] …(+3) | Hierarchy/LoopHierarchyGenerator.lean:46 `Gauss.deriv_expected_gloop_eq_hierarchyCuts`<br>Induction/HierarchyN.lean:31 `Ind.hierarchyN` | internal by DECISIONS §5: Lemma 2.11 of [YY_25] |
| 38 | `Def_Ktza` | Def_Ktza, pro_dyncalK, calGonIND, eq:initial_K, eq:KMloop | 1_2:986 | definition [Tree approximation] | KL | band | iii | Loop/TreeRep.lean:158 `def IsKLoop (m : Bool → ℂ) (T : Set ℝ) (K : ℝ → LoopIdx (Zd d L) → ℂ) : Prop` ⟦#check: `(d L : ℕ) → [NeZero L] → ℕ → ℝ → (Bool → ℂ) → Set ℝ → (ℝ → RBM.Loop.LoopIdx (RBM.Zd d L) → ℂ) → Prop`⟧<br>Loop/TreeRep.lean:151 `noncomputable def MLoop (m : Bool → ℂ) (I : LoopIdx (Zd d L)) : ℂ` ⟦#check: `(d L : ℕ) → [NeZero L] → ℕ → (Bool → ℂ) → RBM.Loop.LoopIdx (RBM.Zd d L) → ℂ`⟧<br>Loop/TreeRep.lean:142 `noncomputable def treeEqRhs (K : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) : ℂ` ⟦#check: `(d L : ℕ) → [NeZero L] → ℕ → ℝ → (RBM.Loop.LoopIdx (RBM.Zd d L) → ℂ) → RBM.Loop.LoopIdx (RBM.Zd d L) → ℂ`⟧<br>Loop/Unique.lean:247 `theorem isKLoop_unique (hL : 3 ≤ L) (m : Bool → ℂ) {T : Set ℝ} {K K' : ℝ → LoopIdx (Zd d L) → ℂ} (hK : IsKLoop d L W g m T K) (hK' : IsKLoop d L W g m T K') {T₀ R : ℝ} (hT : Set.Icc 0 T₀ ⊆ T) (hR0 : 0 ≤ R) (hR : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Zd d L), I.WF → I.length = 2 → ‖K t I‖ ≤ R ∧ ‖K' t I‖ ≤ R) : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (Zd d L), I.WF → 2 ≤ I.length → K t I = K' t I`<br>Loop/Primitive.lean:97 `noncomputable def kTwoLoop (m : Bool → ℂ) (t : ℝ) (I : LoopIdx (Zd d L)) : ℂ` ⟦#check: `(d L : ℕ) → [NeZero L] → ℕ → ℝ → (Bool → ℂ) → ℝ → RBM.Loop.LoopIdx (RBM.Zd d L) → ℂ`⟧<br>Loop/TreeThree.lean:325 `noncomputable def kLoop3 (m : Bool → ℂ) (t : ℝ) (I : LoopIdx (Zd d L)) : ℂ` ⟦#check: `(d L : ℕ) → [NeZero L] → ℕ → ℝ → (Bool → ℂ) → ℝ → RBM.Loop.LoopIdx (RBM.Zd d L) → ℂ`⟧ | predicate form; band closed-form M-loop (BA trace form absent); explicit solution only for n<=3; uniqueness needs the a priori 2-loop bound hbdd | lem_propTH, ML:GtLocal, [sub 3_5:69 Dynamics of (cal L-cal K)-loops], M-graph-value-definition | Loop/Kcal.lean:203 `KLoop.Kcal`<br>Loop/TreeRep.lean:2563 `KLoop.isPrimitive_Kcal`<br>Loop/Unique.lean:276 `KLoop.isPrimitive_eq_Kcal` | internal by DECISIONS §5: [YY_25]@1_2:1010; [RBSO1D]@1_2:1010 |
| 39 | `eq_Ward0` | eq_Ward0 | 1_2:1018 | eq/def | KL | both | iv | none | resolvent Ward identity absent on main (no declaration) | eq_Ward, lem: EMn2_N | Hierarchy/WardResolvent.lean:85 `sum_gloop_two_ward`<br>Hierarchy/WardResolvent.lean:117 `sum_gloop_ward_last` |  |
| 40 | `eq_Ward` | eq_Ward | 1_2:1025 | eq/def | KL | both | iv | none | sum_x \|R_xy\|^2 = Im R_yy/eta absent | (none cited; statement/definition) | Hierarchy/WardResolvent.lean:85 `sum_gloop_two_ward` | internal by DECISIONS §5: [YY_25]@1_2:1032; [RBSO1D]@1_2:1032 |
| 41 | `lem_WI_K` | lem_WI_K, WI_calL, WI_calK | 1_2:1034 | lemma [Ward's identity for cL-loops] | KL | band | iv | none | Ward identities for L- and K-loops absent | eq_Ward, ML:Kbound, lem:newKLK, ygdhmsgq0, [sec 3_5:900 Steps 3 and 4: Sharp maximum estim], ygdhmsgq …(+7) | Loop/Ward.lean:969 `KLoop.Kcal_ward`<br>Hierarchy/WardResolvent.lean:117 `sum_gloop_ward_last` | internal by DECISIONS §5: Lemma 3.6 of [YY_25]; Lemma 3.17 of [RBSO1D] |
| 42 | `ML:Kbound` | ML:Kbound, eq:bcal_k | 1_2:1054 | lemma [Upper bounds on cK-loops] | KL | band | iv | Loop/KBound.lean:74 `def KLoopBound (K : ℝ → LoopIdx (Zd d L) → ℂ) : Prop` ⟦#check: `(d L : ℕ) → ℕ → ℝ → (ℝ → RBM.Loop.LoopIdx (RBM.Zd d L) → ℂ) → Prop`⟧ | only the Prop placeholder KLoopBound (owed, not a theorem); helper inv_pow_pair_le (d>=3 step) is proved | lem_WI_K, ygdhmsgq, lem:SEforLn, lem:STOeq_Qt, lem:improve_exp_aver, lem:LWterm_EXP …(+3) | Loop/KBound.lean:545 `KLoop.Kbound_prec_uncond`<br>Induction/Defs.lean:179 `Ind.KboundConcl` | internal by DECISIONS §5: [YY_25]@A:734; [RBSO1D]@A:734 |
| 43 | `def_Theta` | def_Theta, eq:Msig, def_Thxi, def_Thxi0 | 1_2:1068 | definition | F0 | band | iii | Propagator/Basic.lean:70 `noncomputable def Theta (ξ : ℂ) : Matrix (Zd d L) (Zd d L) ℂ` ⟦#check: `(d L : ℕ) → [NeZero L] → ℝ → ℂ → Matrix (RBM.Zd d L) (RBM.Zd d L) ℂ`⟧<br>Propagator/Basic.lean:225 `noncomputable def Theta0 (ξ : ℂ) : Matrix (Zd d L) (Zd d L) ℂ` ⟦#check: `(d L : ℕ) → [NeZero L] → ℝ → ℂ → Matrix (RBM.Zd d L) (RBM.Zd d L) ℂ`⟧ | band: M^{(s1,s2)} = m(s1)m(s2) I (D6); BA matrix M^{(s1,s2)} absent; Theta_t = Theta d L g (t m(s1)m(s2)) | [sec 1_2:1 Introduction], lem_propTH, DefTHUST | Propagator/Basic.lean:83 `Theta` |  |
| 44 | `defi:ofB#B` | defi:ofB, eq_B_param, eq:BtBt | 1_2:1105 | definition [Definition of B] | F0 | both | i | Defs/Params.lean:36 `noncomputable def Bparam (d L : ℕ) (g t : ℝ) (K : ℕ) : ℝ` ⟦#check: `ℕ → ℕ → ℝ → ℝ → ℕ → ℝ`⟧<br>Defs/Tail.lean:44 `noncomputable def BparamR (r : ℝ) : ℝ` ⟦#check: `ℕ → ℕ → ℝ → ℝ → ℝ → ℝ`⟧ | B_{t,K}; Bparam has natural K, BparamR real K | MR:locSC, MR:QuDiff, MR:decol_BA, ML:Kbound, def_Theta, [sub 1_2:1188 Proof of the main results] …(+2) | Path/Scales.lean:44 `Path.scaleM` — d=2 analogue is M_u (no K dependence) | internal by DECISIONS §5: [DYYY25]@1_2:1116; [yang2024Del]@1_2:1116; [RBSO1D]@1_2:1116 |
| 45 | `defi:ofB#BtBt` | defi:ofB, eq_B_param, eq:BtBt | 1_2:1105 | definition [Definition of B] | F0 | both | iv | none | (eq:BtBt) calB_{eta_t,K} ~ W^{-d} B_{t,K/W} absent | MR:locSC, MR:QuDiff, MR:decol_BA, ML:Kbound, def_Theta, [sub 1_2:1188 Proof of the main results] …(+2) | none | internal by DECISIONS §5: [DYYY25]@1_2:1116; [yang2024Del]@1_2:1116; [RBSO1D]@1_2:1116 |
| 46 | `eq:ellt` | eq:ellt | 1_2:1121 | sub-label/eq | F0 | both | i | Defs/Params.lean:32 `noncomputable def ellT (L : ℕ) (g t : ℝ) : ℝ` ⟦#check: `ℕ → ℝ → ℝ → ℝ`⟧<br>Defs/Params.lean:42 `theorem ellT_le_L {L : ℕ} {g t : ℝ} : ellT L g t ≤ (L : ℝ)`<br>Defs/Params.lean:39 `theorem one_le_ellT {L : ℕ} {g t : ℝ} (hL : 1 ≤ (L : ℝ)) : 1 ≤ ellT L g t` | ell_t; t=1 junk value (D4) | (none cited; statement/definition) | Path/Scales.lean:52 `Path.ellStar` |  |
| 47 | `lem_propTH#1` | lem_propTH, eq:ellt, eq:THETAinftinf, prop:ThfadC, prop:ThfadC_short, prop:BD1, prop:BD2, prop:ThfadC0 | 1_2:1119 | lemma | F0 | band | i | Propagator/Props4.lean:95 `theorem Theta_transpose_of_three_le (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) : (Theta d L g ξ)ᵀ = Theta d L g ξ`<br>Propagator/Basic.lean:114 `theorem Theta_isSymm (hS : ‖SB d L g‖ = 1) {ξ : ℂ} (hξ : ‖ξ‖ < 1) : (Theta d L g ξ).IsSymm` | Symmetry (band: Theta^{(s2,s1)}=Theta^{(s1,s2)} trivially) | MR:QUE, ML:Kbound, defi:ofB, [sub 1_2:1188 Proof of the main results], lem:main_ind, def: TTfunc …(+25) | Propagator/Basic.lean:83 `Theta` | internal by DECISIONS §5: [YY_25]@1_2:1174; [RBSO1D]@1_2:1174; [bourgade2019random]@A:25; [yang2024Del]@A:50 …(+2) |
| 48 | `lem_propTH#2` | lem_propTH, eq:ellt, eq:THETAinftinf, prop:ThfadC, prop:ThfadC_short, prop:BD1, prop:BD2, prop:ThfadC0 | 1_2:1119 | lemma | F0 | band | i | Propagator/Props4.lean:100 `theorem Theta_apply_add_right_of_three_le (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (a b c : Zd d L) : Theta d L g ξ (a + c) (b + c) = Theta d L g ξ a b`<br>Defs/Block.lean:62 `theorem SB_apply_add_right (a b c : Zd d L) : SB d L g (a + c) (b + c) = SB d L g a b` | Translation invariance | MR:QUE, ML:Kbound, defi:ofB, [sub 1_2:1188 Proof of the main results], lem:main_ind, def: TTfunc …(+25) | none (implicit in RBM2D Theta files) | internal by DECISIONS §5: [YY_25]@1_2:1174; [RBSO1D]@1_2:1174; [bourgade2019random]@A:25; [yang2024Del]@A:50 …(+2) |
| 49 | `lem_propTH#3` | lem_propTH, eq:ellt, eq:THETAinftinf, prop:ThfadC, prop:ThfadC_short, prop:BD1, prop:BD2, prop:ThfadC0 | 1_2:1119 | lemma | F0 | band | i | Propagator/Props4.lean:105 `theorem Theta_commute_SB_of_three_le (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) : Commute (Theta d L g ξ) (SB d L g)`<br>Propagator/Props4.lean:110 `theorem Theta_commute_of_three_le (hL : 3 ≤ L) {ξ ξ' : ℂ} (hξ : ‖ξ‖ < 1) (hξ' : ‖ξ'‖ < 1) : Commute (Theta d L g ξ) (Theta d L g ξ')` | Commutativity | MR:QUE, ML:Kbound, defi:ofB, [sub 1_2:1188 Proof of the main results], lem:main_ind, def: TTfunc …(+25) | none | internal by DECISIONS §5: [YY_25]@1_2:1174; [RBSO1D]@1_2:1174; [bourgade2019random]@A:25; [yang2024Del]@A:50 …(+2) |
| 50 | `lem_propTH#4` | lem_propTH, eq:ellt, eq:THETAinftinf, prop:ThfadC, prop:ThfadC_short, prop:BD1, prop:BD2, prop:ThfadC0 | 1_2:1119 | lemma | F0 | band | i | Propagator/Props4.lean:188 `theorem norm_Theta_apply_le (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {m : ℂ} (hm : ‖m‖ = 1) (a b : Zd d L) : ‖Theta d L g ((t : ℂ) * m) a b‖ ≤ (Theta d L g t a b).re`<br>Propagator/Props4.lean:203 `theorem sum_Theta_real_row (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (a : Zd d L) : ∑ b, (Theta d L g t a b).re = (1 - t)⁻¹`<br>Propagator/Props4.lean:210 `theorem sum_norm_Theta_row_le (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {m : ℂ} (hm : ‖m‖ = 1) (a : Zd d L) : ∑ b, ‖Theta d L g ((t : ℂ) * m) a b‖ ≤ (1 - t)⁻¹`<br>Propagator/Props4.lean:218 `theorem norm_Theta_le (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {m : ℂ} (hm : ‖m‖ = 1) : ‖Theta d L g ((t : ℂ) * m)‖ ≤ (1 - t)⁻¹` | (inf->inf)-norm 1/(1-t), \|Theta^{(s1,s2)}_{ab}\| <= Theta^{(+,-)}_{ab} (needs \|m\|=1, 3<=L) | MR:QUE, ML:Kbound, defi:ofB, [sub 1_2:1188 Proof of the main results], lem:main_ind, def: TTfunc …(+25) | Propagator/Bounds.lean:54 `norm_Theta_le`<br>Propagator/Bounds.lean:73 `sum_norm_Theta_row_le` | internal by DECISIONS §5: [YY_25]@1_2:1174; [RBSO1D]@1_2:1174; [bourgade2019random]@A:25; [yang2024Del]@A:50 …(+2) |
| 51 | `lem_propTH#5a` | lem_propTH, eq:ellt, eq:THETAinftinf, prop:ThfadC, prop:ThfadC_short, prop:BD1, prop:BD2, prop:ThfadC0 | 1_2:1119 | lemma | PT | band | iv | Propagator/Interface.lean:77 `def ThetaDecay (d : ℕ) (g : ℝ) (m : ℂ) : Prop` ⟦#check: `ℕ → ℝ → ℂ → Prop`⟧<br>Test/InterfaceShape.lean:237 `theorem thetaDecay_fixedL (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (g : ℝ) {m : ℂ} (hm : ‖m‖ = 1) : ∃ Cd > (0 : ℝ), ∃ cd > (0 : ℝ), ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ a : Zd d L, ‖Theta d L g ((t : ℂ) * m) 0 a‖ ≤ Cd * Bparam d L g t (zdistD d L a) * Real.exp (-cd * (zdistD d L a : ℝ) / ellT L g t)` | Prop only (hypothesis), constants depend on (g,m) (D13); fixed-L certificate (constant depends on L) is class iii | MR:QUE, ML:Kbound, defi:ofB, [sub 1_2:1188 Proof of the main results], lem:main_ind, def: TTfunc …(+25) | Propagator/Prop5.lean:82 `Theta_prop5_prec`<br>Propagator/Prop5.lean:29 `norm_Theta_apply_le_prop5` | internal by DECISIONS §5: [YY_25]@1_2:1174; [RBSO1D]@1_2:1174; [bourgade2019random]@A:25; [yang2024Del]@A:50; [DYYY25] Lemma 2.14, §8; [Lawler_book] §2 |
| 52 | `lem_propTH#5b` | lem_propTH, eq:ellt, eq:THETAinftinf, prop:ThfadC, prop:ThfadC_short, prop:BD1, prop:BD2, prop:ThfadC0 | 1_2:1119 | lemma | PT | band | iv | Propagator/Interface.lean:101 `def ThetaDecayShort (d : ℕ) (g : ℝ) (m : ℂ) : Prop` ⟦#check: `ℕ → ℝ → ℂ → Prop`⟧<br>Test/InterfaceShape.lean:49 `theorem not_decayShort_at_one (k : ℕ) {g : ℝ} (hg : 0 < g) : ¬ ∃ Cκ > (0 : ℝ), ∃ cκ > (0 : ℝ), ∀ (L : ℕ) (_ : 3 ≤ L) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd (k + 2) L, haveI : NeZero L` | Prop only; constants depend on (g,m); m^2 vs kappa uniformity absent | MR:QUE, ML:Kbound, defi:ofB, [sub 1_2:1188 Proof of the main results], lem:main_ind, def: TTfunc …(+25) | Loop/PropHyp.lean:63 `KLoop.prop5Hyp_holds`<br>Loop/Kcal.lean:340 `KLoop.Prop5Hyp` | internal by DECISIONS §5: [YY_25]@1_2:1174; [RBSO1D]@1_2:1174; [yang2024Del]@A:50; [DYYY25]@A:58 …(+1); [bourgade2019random] Lemma 4.2 |
| 53 | `lem_propTH#6` | lem_propTH, eq:ellt, eq:THETAinftinf, prop:ThfadC, prop:ThfadC_short, prop:BD1, prop:BD2, prop:ThfadC0 | 1_2:1119 | lemma | PT | band | iv | Propagator/Interface.lean:118 `def ThetaDiffOne (d : ℕ) (g : ℝ) (m : ℂ) : Prop` ⟦#check: `ℕ → ℝ → ℂ → Prop`⟧<br>Test/InterfaceShape.lean:437 `theorem thetaDiffOne_fixedL (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (g : ℝ) (hg : 0 < g) {m : ℂ} (hm : ‖m‖ = 1) {τ : ℝ} (hτ : 0 ≤ τ) : ∃ C > (0 : ℝ), ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ a r : Zd d L, ‖Theta d L g ((t : ℂ) * m) 0 (a + r) - Theta d L g ((t : ℂ) * m) 0 a‖ ≤ C * (L : ℝ) ^ τ * (g ^ 2 + \|1 - t\|)⁻¹ * (zdistD d L r : ℝ) * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹` | Prop only; L^tau for N^tau; constants depend on (g,m,c,tau); fixed-L certificate class iii | MR:QUE, ML:Kbound, defi:ofB, [sub 1_2:1188 Proof of the main results], lem:main_ind, def: TTfunc …(+25) | Propagator/Prop6.lean:92 `Theta_prop6_prec` | internal by DECISIONS §5: [YY_25]@1_2:1174; [bourgade2019random]@A:25; [DYYY25]@A:58; [Lawler_book]@A:62; [yang2024Del] Lemma 3.1 (analogous); [RBSO1D] Lemma 3.10, App. B |
| 54 | `lem_propTH#7` | lem_propTH, eq:ellt, eq:THETAinftinf, prop:ThfadC, prop:ThfadC_short, prop:BD1, prop:BD2, prop:ThfadC0 | 1_2:1119 | lemma | PT | band | iv | Propagator/Interface.lean:133 `def ThetaDiffTwo (d : ℕ) (g : ℝ) (m : ℂ) : Prop` ⟦#check: `ℕ → ℝ → ℂ → Prop`⟧<br>Test/InterfaceShape.lean:485 `theorem thetaDiffTwo_fixedL (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (g : ℝ) (hg : 0 < g) {m : ℂ} (hm : ‖m‖ = 1) {τ : ℝ} (hτ : 0 ≤ τ) : ∃ C > (0 : ℝ), ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ a r : Zd d L, ‖Theta d L g ((t : ℂ) * m) 0 (a + r) + Theta d L g ((t : ℂ) * m) 0 (a - r) - 2 * Theta d L g ((t : ℂ) * m) 0 a‖ ≤ C * (L : ℝ) ^ τ * (g ^ 2 + \|1 - t\|)⁻¹ * (zdistD d L r : ℝ) ^ 2 * (((zdistD d L a : ℝ) + 1) ^ d)⁻¹` | Prop only; same shape as #6 | MR:QUE, ML:Kbound, defi:ofB, [sub 1_2:1188 Proof of the main results], lem:main_ind, def: TTfunc …(+25) | Propagator/Prop6.lean:92 `Theta_prop6_prec` | internal by DECISIONS §5: [YY_25]@1_2:1174; [RBSO1D]@1_2:1174; [bourgade2019random]@A:25; [DYYY25]@A:58 …(+1); [yang2024Del] (E.19) |
| 55 | `lem_propTH#8` | lem_propTH, eq:ellt, eq:THETAinftinf, prop:ThfadC, prop:ThfadC_short, prop:BD1, prop:BD2, prop:ThfadC0 | 1_2:1119 | lemma | PT | band | iv | Propagator/Interface.lean:149 `def ThetaZeroMode (d : ℕ) (g : ℝ) (m : ℂ) : Prop` ⟦#check: `ℕ → ℝ → ℂ → Prop`⟧<br>Test/InterfaceShape.lean:372 `theorem thetaZeroMode_fixedL (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (g : ℝ) (hg : 0 < g) {m : ℂ} (hm : ‖m‖ = 1) {τ : ℝ} (hτ : 0 ≤ τ) : ∃ C > (0 : ℝ), ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ a : Zd d L, ‖Theta0 d L g ((t : ℂ) * m) 0 a‖ ≤ C * (L : ℝ) ^ τ * (g ^ 2 + \|1 - t\|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹`<br>Propagator/Gap.lean:501 `theorem exists_norm_Theta0_le (hL : 3 ≤ L) (hg : 0 < g) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℂ, ‖ξ‖ < 1 → ∀ a b : Zd d L, ‖Theta0 d L g ξ a b‖ ≤ C` | Prop only; fixed-L bounds (constant depends on L) are class iii | MR:QUE, ML:Kbound, defi:ofB, [sub 1_2:1188 Proof of the main results], lem:main_ind, def: TTfunc …(+25) | none (d=2: no zero-mode-removed Theta; RBM2D uses sum-zero Q_t) | internal by DECISIONS §5: [YY_25]@1_2:1174; [RBSO1D]@1_2:1174; [bourgade2019random]@A:25; [DYYY25]@A:58 …(+1); [yang2024Del] Lemma 3.1 |
| 56 | `Kn2sol` | Kn2sol, Kn3sol | 1_2:1173 | example | KL | band | ii | Loop/Unique.lean:297 `theorem kTwoFormula_of_isKLoop (hL : 3 ≤ L) (hW : (W : ℂ) ^ d ≠ 0) {m : Bool → ℂ} (hm : ∀ s, ‖m s‖ = 1) {K : ℝ → LoopIdx (Zd d L) → ℂ} (hK : IsKLoop d L W g m (Set.Ico 0 1) K) (hbdd : TwoLoopBounded d L K) : KTwoFormula d L W g m K`<br>Loop/PureLoop.lean:244 `def KTwoFormula (m : Bool → ℂ) (K : ℝ → LoopIdx (Zd d L) → ℂ) : Prop` ⟦#check: `(d L : ℕ) → [NeZero L] → ℕ → ℝ → (Bool → ℂ) → (ℝ → RBM.Loop.LoopIdx (RBM.Zd d L) → ℂ) → Prop`⟧<br>Loop/Primitive.lean:97 `noncomputable def kTwoLoop (m : Bool → ℂ) (t : ℝ) (I : LoopIdx (Zd d L)) : ℂ` ⟦#check: `(d L : ℕ) → [NeZero L] → ℕ → ℝ → (Bool → ℂ) → ℝ → RBM.Loop.LoopIdx (RBM.Zd d L) → ℂ`⟧<br>Loop/Primitive.lean:120 `theorem kTwoFormula_kTwoLoop (m : Bool → ℂ) : KTwoFormula d L W g m (kTwoLoop d L W g m)` | unproved hypothesis: TwoLoopBounded (owed, provable: twoLoopBounded_kTwoLoop only for the explicit family) | MR:locSC, MR:QuDiff, MR:decol_BA, ML:Kbound, DefTHUST, lem: EMn2_N …(+3) | Loop/TreeRep.lean:2563 `KLoop.isPrimitive_Kcal` | internal by DECISIONS §5: [YY_25], [RBSO1D] (as shown in) |
| 57 | `Kn3sol` | Kn3sol | 1_2:1176 | sub-label/eq | KL | band | ii | Loop/TreeThree.lean:350 `theorem kThree_eq_of_isKLoop (hL : 3 ≤ L) (hW : (W : ℂ) ^ d ≠ 0) {m : Bool → ℂ} (hm : ∀ s, ‖m s‖ = 1) {K : ℝ → LoopIdx (Zd d L) → ℂ} (hK : IsKLoop d L W g m (Set.Ico 0 1) K) (hbdd : TwoLoopBounded d L K) : ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ₀ σ₁ σ₂ : Bool) (a₀ a₁ a₂ : Zd d L), K t ⟨[σ₀, σ₁, σ₂], [a₀, a₁, a₂]⟩ = kThree d L W g m t σ₀ σ₁ σ₂ a₀ a₁ a₂`<br>Loop/TreeThree.lean:102 `noncomputable def kThree (m : Bool → ℂ) (t : ℝ) (σ₀ σ₁ σ₂ : Bool) (a₀ a₁ a₂ : Zd d L) : ℂ` ⟦#check: `(d L : ℕ) → [NeZero L] → ℕ → ℝ → (Bool → ℂ) → ℝ → Bool → Bool → Bool → RBM.Zd d L → RBM.Zd d L → RBM.Zd d L → ℂ`⟧ | unproved hypothesis: TwoLoopBounded (owed) | (none cited; statement/definition) | Loop/TreeRep.lean:2563 `KLoop.isPrimitive_Kcal` | internal by DECISIONS §5: [YY_25], [RBSO1D] (as shown in) |
| 58 | `ML:GLoop` | ML:GLoop, Eq:L-KGt, Eq:L-KGt2 | 1_2:1193 | lemma [G-loop estimates] | ST | both | iv | none | G-loop estimates; nothing on main | MR:locSC, MR:QuDiff, MR:decol_BA, ML:GLoop_expec, ML:GtLocal, lem:main_ind …(+4) | Induction/Defs.lean:308 `Ind.MLConcl`<br>Induction/Defs.lean:302 `Ind.MainIndConcl` — RBM2D states the same result as MLConcl (per-time Prop) |  |
| 59 | `ML:GLoop_expec` | ML:GLoop_expec, Eq:Gdecay, Eq:Gtlp_exp | 1_2:1203 | lemma [2-loop estimates] | ST | both | iv | none | 2-loop pointwise + expected estimates | MR:locSC, MR:QuDiff, ML:GLoop, ML:GtLocal, lem:main_ind, Eq:Gdecay_flow …(+1) | Evolution/Defs.lean:138 `Evol.MLExpConcl`<br>Induction/Defs.lean:308 `Ind.MLConcl` |  |
| 60 | `ML:GtLocal` | ML:GtLocal, Gt_bound | 1_2:1217 | lemma [Local law for Gt] | ST | both | iv | none | entrywise local law for G_t | MR:locSC, MR:QuDiff, MR:decol_BA, ML:GLoop, ML:GLoop_expec, lem:main_ind …(+2) | Induction/Defs.lean:329 `Ind.GtLocalRegionPT`<br>Induction/Defs.lean:338 `Ind.GtLocalRegionUnif` |  |
| 61 | `lem:main_ind` | lem:main_ind, Eq:L-KGt+IND, Eq:Gdecay+IND, Eq:Gdecay+IND_s<g, Gt_bound+IND, Eq:Gtlp_exp+IND, con_st_ind, Eq:Gdecay+s<g | 1_2:1256 | theorem | ST | both | iv | none | inductive step; d>=3 needs new intervals lambda^2/L^d <= 1-t <= lambda^2/L^2 (DECISIONS 7) | ML:GLoop, ML:GLoop_expec, ML:GtLocal, Gt_avgbound_flow, Eq:Gdecay_w, Eq:LGxb …(+26) | Induction/Defs.lean:229 `Ind.MainIndHyp`<br>Induction/Defs.lean:302 `Ind.MainIndConcl`<br>Induction/MainInd.lean:110 `Ind.mainIndPinV3_of_R3` |  |
| 62 | `lRB1` | lRB1 | 1_2:1321 | eq/def | ST | both | iv | none | Step 1 (a priori G-loop bound) | lem_ConArg, [Step2-proof: proof@3_5:454], lem:STOeq_Qt, lem:iterations, lem_ConArg_BA | Induction/Step1.lean:1378 `Ind.step1` | internal by DECISIONS §5: [YY_25] §5.1 (3_5:40, 65) |
| 63 | `Gtmwc` | Gtmwc | 1_2:1327 | eq/def | ST | both | iv | none | Step 1 (weak local law) | lem_ConArg, lem:newKLK, [Step2-proof: proof@3_5:454], eq:def2_stopping, lem_ConArg_BA | Induction/Step1.lean:1378 `Ind.step1` | internal by DECISIONS §5: [YY_25] §5.1 (3_5:40, 65) |
| 64 | `Gt_bound_flow` | Gt_bound_flow | 1_2:1342 | eq/def | ST | both | iv | none | Step 2 local law | [Step2-proof: 3_5:302], [Step2-proof: proof@3_5:454], lem:SEforLn, lem_decayLoop, lem:STOeq_NQ, lem:STOeq_Qt …(+5) | Path/Step2Close.lean:49 `Path.Step2ClosureV3`<br>Path/Step2Close.lean:56 `Path.step2Eq53PTV3_of_gridStep2Eq53PT` — d=2 route (Gronwall on J_{u,D}) differs from the d>=3 argument (lem:newKLK + eq:Gronwall_dervJuD) |  |
| 65 | `Gt_avgbound_flow` | Gt_avgbound_flow | 1_2:1344 | eq/def | ST | both | iv | none | Step 2 averaged law | [Step2-proof: 3_5:302], [Step2-proof: proof@3_5:454], lem:SEforLn, lem:STOeq_Qt, lem:iterations, lem:STOeq_Qt_nonzero …(+7) | Path/Step2Close.lean:49 `Path.Step2ClosureV3` |  |
| 66 | `Eq:Gdecay_w` | Eq:Gdecay_w | 1_2:1349 | eq/def | ST | both | iv | none | Step 2 2-loop decay with loss ((1-s)/(1-u))^{C_d} | [Step2-proof: 3_5:302], awi2iks, [Step2-proof: proof@3_5:454], eq:def2_stopping, [sec 3_5:900 Steps 3 and 4: Sharp maximum estim], lem:SEforLn …(+11) | Path/Step2Grid.lean:763 `Path.gridStep2PT`<br>Path/Step2Close.lean:49 `Path.Step2ClosureV3` |  |
| 67 | `Eq:LGxb` | Eq:LGxb | 1_2:1361 | eq/def | ST | both | iv | none | Step 3 sharp n-loop bound | lem:STOeq_Qt, lem:iterations, [Step4-proof: 3_5:1602] | Induction/Step3.lean:1777 `Ind.step3` |  |
| 68 | `Eq:L-KGt-flow` | Eq:L-KGt-flow | 1_2:1371 | eq/def | ST | both | iv | none | Step 4 (L-K)-loop estimate | [Step4-proof: 3_5:1602], [sec 3_5:1935 Step 5: Pointwise estimate for (cL], [sub 3_5:2284 The case 1-t ge g2], lem_dec_calE, lem:pf_step5, lem:improve_exp_aver …(+1) | Induction/Step45.lean:1188 `Ind.step4` |  |
| 69 | `Eq:Gdecay_flow` | Eq:Gdecay_flow | 1_2:1380 | eq/def | ST | both | iv | none | Step 5 pointwise 2-loop estimate | lem: EMn2_N, [sub 3_5:1957 The case g2/L2le 1- tle 1-s le g2], [sub 3_5:2251 The case g2/Ld leq 1-t leq 1-s leq], lem:pf_step5, lem:improve_exp_aver, lem:LWterm_EXP | Induction/Step45.lean:1258 `Ind.step5` | internal by DECISIONS §5: [YY_25] §5.3; [DYYY25] §7 (CLT) |
| 70 | `Eq:Gdecay+s<g_flow` | Eq:Gdecay+s<g_flow | 1_2:1384 | eq/def | ST | both | iv | none | Step 5 for 1-t >= lambda^2 | [sub 3_5:2284 The case 1-t ge g2], lem:pf_step5 | Induction/Step45.lean:1258 `Ind.step5` | internal by DECISIONS §5: [YY_25] §5.3 (3_5:2287) |
| 71 | `Eq:Gtlp_exp_flow` | Eq:Gtlp_exp_flow | 1_2:1392 | eq/def | ST | both | iv | none | Step 6 expected 2-loop estimate | lem:LWterm_EXP, [Step6-proof: proof@6:93] | Induction/MainInd.lean:159 `Ind.mlExp`<br>Evolution/Step61.lean:853 `Evol.step61` |  |
| 72 | `lem_GbEXP` | lem_GbEXP, def_asGMc, GiiGEX, GijGEX, initialGT2, GavLGEX | 3_5:14 | lemma | ST | band | iv | none | entrywise/averaged local law from 2-loops | [Step1-proof: 3_5:9], lem_ConArg, [Step2-proof: 3_5:302], lem:LWterm, lem: EWGn2_N, lem: EMn2_N …(+11) | Green/GbEXP.lean:45 `Green.gbEXPV3`<br>Green/GbEXP.lean:62 `Green.GbEXP_check_hyp` | internal by DECISIONS §5: Lemma 4.1 of [YY_25]; other cited keys in the row region (outside the DECISIONS §2 inventory): [erdHos2012rigidity]@3_5:37, [erdos2013delocalization]@3_5:37 |
| 73 | `lem_ConArg` | lem_ConArg, eq:loopbound_s, res_lo_bo_eta | 3_5:42 | lemma | ST | band | iv | none | continuity argument for G-loops | lem:STOeq_Qt, lem:STOeq_Qt_nonzero, lem_ConArg_BA | Induction/ConArg.lean:613 `Ind.conArg`<br>Induction/ConArg.lean:61 `Ind.ConArgPin` | internal by DECISIONS §5: Lemma 5.1 of [YY_25] |
| 74 | `eq_L-Keee` | eq_L-Keee | 3_5:73 | eq/def | ST | both | iv | none | SDE for (L-K)-loops | def_ELKLK, DefTHUST, Sol_CalL, lem_+Q, lem: newPQ | Induction/HierarchyN.lean:31 `Ind.hierarchyN` | internal by DECISIONS §5: eq. (5.12) of [YY_25] |
| 75 | `DefKsimLK` | DefKsimLK | 3_5:89 | eq/def | ST | both | iv | none | K^(l) ~ (L-K) operator | [sec 3_5:900 Steps 3 and 4: Sharp maximum estim], lem:SEforLn | Induction/HierarchyN.lean:31 `Ind.hierarchyN` |  |
| 76 | `def_ELKLK` | def_ELKLK | 3_5:97 | eq/def | ST | both | iv | none | quadratic (L-K)x(L-K) term | [sec 3_5:900 Steps 3 and 4: Sharp maximum estim], lem:SEforLn | Induction/HierarchyN.lean:31 `Ind.hierarchyN` |  |
| 77 | `DefTHUST` | DefTHUST, def:op_thn, def_Ustz | 3_5:109 | definition [Evolution kernel] | EK | band | iii | Kernel/Evolution.lean:52 `noncomputable def thetaKer (μ : ℂ) (t : ℝ) : Matrix (Zd d L) (Zd d L) ℂ` ⟦#check: `(d L : ℕ) → [NeZero L] → ℝ → ℂ → ℝ → Matrix (RBM.Zd d L) (RBM.Zd d L) ℂ`⟧<br>Kernel/Evolution.lean:56 `noncomputable def uKer (μ : ℂ) (s t : ℝ) : Matrix (Zd d L) (Zd d L) ℂ` ⟦#check: `(d L : ℕ) → [NeZero L] → ℝ → ℂ → ℝ → ℝ → Matrix (RBM.Zd d L) (RBM.Zd d L) ℂ`⟧<br>Kernel/Evolution.lean:60 `noncomputable def ThetaN {n : ℕ} (m : Fin n → ℂ) (t : ℝ) (A : (Fin n → Zd d L) → ℂ) : (Fin n → Zd d L) → ℂ` ⟦#check: `(d L : ℕ) → [NeZero L] → ℝ → {n : ℕ} → (Fin n → ℂ) → ℝ → ((Fin n → RBM.Zd d L) → ℂ) → (Fin n → RBM.Zd d L) → ℂ`⟧<br>Kernel/Evolution.lean:65 `noncomputable def UN {n : ℕ} (m : Fin n → ℂ) (s t : ℝ) (A : (Fin n → Zd d L) → ℂ) : (Fin n → Zd d L) → ℂ` ⟦#check: `(d L : ℕ) → [NeZero L] → ℝ → {n : ℕ} → (Fin n → ℂ) → ℝ → ℝ → ((Fin n → RBM.Zd d L) → ℂ) → (Fin n → RBM.Zd d L) → ℂ`⟧<br>Kernel/Evolution.lean:49 `def cycProd {n : ℕ} (m : Fin n → ℂ) (i : Fin n) : ℂ` ⟦#check: `{n : ℕ} → (Fin n → ℂ) → Fin n → ℂ`⟧ | band: M^{(s_i,s_{i+1})} = m m scalar via cycProd; BA matrix version absent | lem:DIfREP, lem:newKLK, Def:QtPt, lem_+Q, lem:STOeq_Qt, lem: newPQ …(+4) | Path/UBounds.lean:52 `Path.thetaGen`<br>Path/Kernel.lean:47 `Path.Uop`<br>Path/Kernel.lean:42 `Path.ukerMat` |  |
| 78 | `Sol_CalL` | Sol_CalL, int_K-L_ST, int_K-LcalE | 3_5:134 | lemma [Integrated loop hierarchy, L] | ST | both | iv | none | integrated hierarchy / Duhamel with stopping time | awi2iks, eq:def2_stopping, [sec 3_5:900 Steps 3 and 4: Sharp maximum estim], def:XIL-K, lem:SEforLn, lem:STOeq_NQ …(+4) | Induction/HierarchyN.lean:31 `Ind.hierarchyN`<br>Path/Kernel.lean:47 `Path.Uop` | internal by DECISIONS §5: Lemma 5.3 of [YY_25] |
| 79 | `def:CALE` | def:CALE, defEOTE, def_diffakn_k | 3_5:169 | definition [Quadratic variation loop] | ST | both | iv | none | quadratic-variation loop (E x E)^M | lem: EMn2_N, [sec 3_5:900 Steps 3 and 4: Sharp maximum estim], lem:SEforLn | Path/QVIdentity.lean:357 `Path.QVPropagated`<br>Path/QVForm.lean:251 `Path.v_gradMat_eq_quadVar` |  |
| 80 | `lem:DIfREP` | lem:DIfREP, aaswtghh, alu9_STime | 3_5:218 | lemma [Lemma 5.5 of citeYY25] | ST | both | iv | none | BDG: RBM2D uses Azuma-Hoeffding + Doob on the grid (DECISIONS 7) | [Step2-proof: proof@3_5:454], lem:STOeq_NQ, lem:STOeq_Qt_nonzero, [sub 3_5:1957 The case g2/L2le 1- tle 1-s le g2], lem_ConArg_BA | Path/DuhamelTail.lean:849 `Path.stoppedAzuma108`<br>Path/Azuma.lean:84 `Path.azuma_complex`<br>Path/Azuma.lean:212 `Path.doob_L2_max` | internal by DECISIONS §5: Lemma 5.5 of [YY_25] |
| 81 | `def: TTfunc` | def: TTfunc, defTUL, defWTTlD | 3_5:311 | definition [Tail functions] | EK | both | i | Defs/Tail.lean:48 `noncomputable def tailT (r : ℝ) : ℝ` ⟦#check: `ℕ → ℕ → ℝ → ℝ → ℝ → ℝ`⟧<br>Defs/Tail.lean:52 `noncomputable def tailW (ℓ W D r : ℝ) : ℝ` ⟦#check: `ℕ → ℕ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ`⟧<br>Defs/Tail.lean:44 `noncomputable def BparamR (r : ℝ) : ℝ` ⟦#check: `ℕ → ℕ → ℝ → ℝ → ℝ → ℝ`⟧ | T_t(r) and wT^l_{t,D}(r) | lem:newKLK, lem: EWGn2_N, ygdhmsgq0, [sec 7_8:1 Estimation of the light-weight ter] | Path/Scales.lean:48 `Path.tailT`<br>Path/Scales.lean:52 `Path.ellStar` |  |
| 82 | `lem:propT` | lem:propT, TTT2 | 3_5:328 | lemma [Property of cal T] | EK | both | i | Kernel/PropT.lean:409 `theorem propT (k : ℕ) : ∃ C > (0 : ℝ), ∀ (L : ℕ) [NeZero L] (g u t : ℝ), 0 < g → 0 ≤ u → u ≤ t → t < 1 → (g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t ∨ 1 - u ≤ g ^ 2 / (L : ℝ) ^ 2) → ∀ a b : Zd (k + 2) L, ∑ c : Zd (k + 2) L, tailT (k + 2) L g u (zdistD (k + 2) L (a - c)) * tailT (k + 2) L g t (zdistD (k + 2) L (c - b)) ≤ C / (1 - u) * tailT (k + 2) L g t (zdistD (k + 2) L (a - b))`<br>Kernel/PropT.lean:333 `theorem propT_i [NeZero L] (hg : 0 < g) (hut : u ≤ t) (ht : t < 1) (h : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t) (a b : Zd (k + 2) L) : ∑ c : Zd (k + 2) L, tailT (k + 2) L g u (zdistD (k + 2) L (a - c)) * tailT (k + 2) L g t (zdistD (k + 2) L (c - b)) ≤ constI k / (1 - u) * tailT (k + 2) L g t (zdistD (k + 2) L (a - b))`<br>Kernel/PropT.lean:126 `theorem propT_ii [NeZero L] (hg : 0 < g) (hut : u ≤ t) (ht : t < 1) (h : 1 - u ≤ g ^ 2 / (L : ℝ) ^ 2) (a b : Zd (k + 2) L) : ∑ c : Zd (k + 2) L, tailT (k + 2) L g u (zdistD (k + 2) L (a - c)) * tailT (k + 2) L g t (zdistD (k + 2) L (c - b)) ≤ constII k / (1 - u) * tailT (k + 2) L g t (zdistD (k + 2) L (a - b))` | C depends only on k (d=k+2), uniform in L,g,u,t; hypotheses 0<g, 0<=u<=t<1 and the two regimes of the paper | def: TTfunc, lem:newKLK, ygdhmsgq0, [sub 3_5:1957 The case g2/L2le 1- tle 1-s le g2], lem:LW_moment_exp_near | Path/TailSums.lean:505 `Path.convTailT`<br>Path/TailSums.lean:465 `Path.convExpSqrt` |  |
| 83 | `awi2iks` | awi2iks | 3_5:346 | eq/def | ST | both | iv | none | Step 2 self-improving scheme | eq:def2_stopping | Path/Step2Close.lean:49 `Path.Step2ClosureV3` |  |
| 84 | `LK_simple` | LK_simple | 3_5:360 | eq/def | ST | both | iv | none | n=2 integral equation | defCALJ, lem: EMn2_N, [Step2-proof: proof@3_5:454] | Induction/HierarchyN.lean:31 `Ind.hierarchyN` |  |
| 85 | `defCALJ` | defCALJ | 3_5:365 | eq/def | ST | both | iv | none | random control J^l_{u,D} | lem:newKLK, [Step2-proof: proof@3_5:454], eq:def2_stopping, ygdhmsgq0 | Path/GoodSet.lean:49 `Path.goodSet`<br>Path/GoodSet.lean:67 `Path.GoodSetPT` |  |
| 86 | `lem:newKLK` | lem:newKLK, juwo2=klk, juwo=Lklk | 3_5:371 | lemma | ST | both | iv | none | (Theta o (L-K)) and (L-K)x(L-K) bounds via lem:propT | defCALJ, lem: EMn2_N, [Step2-proof: proof@3_5:454], eq:def2_stopping, lem_ConArg_BA | none (d=2: J_{u,D} Gronwall, Path/Step2*) |  |
| 87 | `lem:LWterm` | lem:LWterm, eq:LW_assm, eq:Psi, eq:LW_conclusion, eq:LW_conclusion2 | 3_5:385 | lemma [Light-weight estimate: B-bou] | LW | both | iv | none | light-weight E^{Gc} bound (B-bound); graphical expansion | [sec 3_5:1 Steps 1 and 2: A priori G-loop est], lem:newKLK, lem: EWGn2_N, lem: EMn2_N, [Step2-proof: proof@3_5:454], eq:def2_stopping …(+8) | none (d=2 treats E^{Gc} by large deviation / IBP: Green/*) | internal by DECISIONS §5: [yang2021delocalization], [yang2021random] (3_5:423) |
| 88 | `lem: EWGn2_N` | lem: EWGn2_N, eq:LW_assm_exp, eq:LW_conclusion_exp | 3_5:406 | lemma [Light-weight estimate: cal T] | LW | both | iv | none | light-weight E^{Gc} bound (T-bound); d=2 analogue is lem_dec_calE (wG part) | [sec 3_5:1 Steps 1 and 2: A priori G-loop est], lem:newKLK, lem:LWterm, lem: EMn2_N, [Step2-proof: proof@3_5:454], eq:def2_stopping …(+8) | Path/LemDecCalEwG.lean:1276 `Path.lemDecCalE_wG` | internal by DECISIONS §5: [yang2021delocalization]@3_5:423; [yang2021random]@3_5:423 |
| 89 | `rmk:poly_exp` | rmk:poly_exp | 3_5:416 | remark | - | - | iv | none | remark (why T-bound is not a corollary of B-bound) | (none cited; statement/definition) | - |  |
| 90 | `lem: EMn2_N` | lem: EMn2_N, eq:MG_conclusion, eq:MG_conclusion2, eq:MG_conclusion3 | 3_5:427 | lemma [Martingale estimate] | ST | both | iv | none | martingale quadratic-variation bound | [sec 1_2:1 Introduction], lem: EWGn2_N, [Step2-proof: proof@3_5:454], ygdhmsgq0, [sec 3_5:1935 Step 5: Pointwise estimate for (cL], [sub 3_5:1957 The case g2/L2le 1- tle 1-s le g2] …(+3) | Path/LemDecCalEdif.lean:1632 `Path.lemDecCalE_dif`<br>Path/QVIdentity.lean:487 `Path.qvPropagated` — d=2 analogue lem_dec_calE (dif part), different proof |  |
| 91 | `rmk_bottleneck` | rmk_bottleneck | 3_5:446 | remark | - | - | iv | none | remark (exponent 1/5) | Eq:Gdecay_w, lem:localregular | - |  |
| 92 | `eq:opt_L2` | eq:opt_L2 | 3_5:470 | eq/def | ST | both | iv | none | Step 2 max bound W^{-d}B_{u,0} | [Step2-proof: proof@3_5:454] | Path/Step2Close.lean:49 `Path.Step2ClosureV3` |  |
| 93 | `Gronwall_inequality` | Gronwall_inequality | 3_5:493 | eq/def | ST | both | iv | none | classical Gronwall (Mathlib: norm_le_gronwallBound et al.; Loop/Unique imports Mathlib.Analysis.ODE.Gronwall) | [Step2-proof: proof@3_5:454] | uses Mathlib Gronwall |  |
| 94 | `eq:simpleboundK` | eq:simpleboundK | 3_5:518 | eq/def | ST | both | iv | none | K^(2) tail bound from (prop:ThfadC)+(Kn2sol) | [Step2-proof: proof@3_5:454] | Path/KellStar.lean:311 `Path.kellStarEv` |  |
| 95 | `eq:Gronwall_dervJuD` | eq:Gronwall_dervJuD | 3_5:529 | eq/def | ST | both | iv | none | Gronwall bound for J under the stopping time | [Step2-proof: proof@3_5:454] | Path/Step2Close.lean:49 `Path.Step2ClosureV3` |  |
| 96 | `eq:def2_stopping` | eq:def2_stopping | 3_5:533 | eq/def | ST | both | iv | none | stopping time of Step 2 (needs the grid path, DECISIONS 7) | [Step2-proof: proof@3_5:454] | Path/Step2Close.lean:49 `Path.Step2ClosureV3` | internal by DECISIONS §5: [YY_25]@3_5:582; [DYYY25]@3_5:582; other cited keys in the row region (outside the DECISIONS §2 inventory): [erdHos2025zigzag]@3_5:582 |
| 97 | `ygdhmsgq0` | ygdhmsgq0, eq_sym_loop_bound, eq_sym_loop_bound2 | 3_5:751 | lemma | ST | both | iv | none | pointwise contract inequality for the symmetric 6-loop | [Step2-proof: 3_5:302], lem: EMn2_N, [sec 3_5:900 Steps 3 and 4: Sharp maximum estim] | none (d>=3 only) |  |
| 98 | `ygdhmsgq` | ygdhmsgq, yi2oslxj2, u2jzooi-2 | 3_5:923 | lemma | ST | both | iv | none | contract inequality (Cauchy-Schwarz + Ward) | [sec 1_2:1 Introduction], lem: EMn2_N, [sec 3_5:900 Steps 3 and 4: Sharp maximum estim], def:XIL-K, lem:SEforLn | none (d>=3 only) |  |
| 99 | `lem_wardineq_K` | lem_wardineq_K, wardineq_K | 3_5:1001 | lemma | KL | band | iv | none | sum_{a_n}\|K^(n)\| bound; proved in A.5 (not literally named in ROUTES) | def:XIL-K, lem:SEforLn, [sub A:315 Basic properties of cal K-loops], lem_pureloop | Loop/SumAll.lean:749 `KLoop.Kcal_sumAll_le` |  |
| 100 | `def:XiL` | def:XiL | 3_5:1010 | eq/def | ST | both | iv | none | Xi^(L) parameters (sup of loops) | lem:SEforLn, lem:STOeq_NQ | none |  |
| 101 | `def:XIL-K` | def:XIL-K | 3_5:1012 | eq/def | ST | both | iv | none | Xi^(L-K) parameters | lem:SEforLn, Def:QtPt | none |  |
| 102 | `lem:SEforLn` | lem:SEforLn, bEwGn, eq:KsimL-K, eq:L-KsimL-K, eq:MG_nloop | 3_5:1017 | lemma [Estimates of cal E terms] | ST | both | iv | none | estimates of E terms (Step 3) | [sec 3_5:900 Steps 3 and 4: Sharp maximum estim], lem_decayLoop, lem:STOeq_NQ, lem_+Q, lem:STOeq_Qt, lem: newPQ …(+1) | none (RBM2D Step3.lean is a deterministic calculus) | internal by DECISIONS §5: [YY_25]@3_5:1105 |
| 103 | `Def_decay` | Def_decay, deccA | 3_5:1115 | definition [Fast decay property] | ST | both | iv | none | fast decay property | (none cited; statement/definition) | Induction/DecayLoop.lean:690 `Ind.decayLoopAt` |  |
| 104 | `lem_decayLoop` | lem_decayLoop, res_decayLK | 3_5:1126 | claim | ST | both | iv | none | L- and K-loops have the decay property | lem:STOeq_NQ | Induction/DecayLoop.lean:690 `Ind.decayLoopAt`<br>Induction/DecayLoop.lean:711 `Ind.decayLoopWindow` |  |
| 105 | `lem:STOeq_NQ` | lem:STOeq_NQ, NALsigm, am;asoiuw | 3_5:1136 | lemma [Non-alternating loops] | ST | both | iv | none | non-alternating loops (Step 3) | lem_+Q, lem:STOeq_Qt | Induction/Step3.lean:1777 `Ind.step3` |  |
| 106 | `Def:QtPt` | Def:QtPt, eq:sumzero_op, eq:suma1chi, eq:derv_Theta, eq:sum0PA | 3_5:1204 | definition [Partial sum and sum-zero ope] | ST | both | iv | none | partial sum P and sum-zero Q_t with mollifier | lem_+Q, lem:STOeq_Qt, [Step6-proof: proof@6:93] | Induction/QopBounds.lean:622 `Ind.qopDecay` — RBM2D has Q_t (Induction/SumZeroQ, QopBounds) |  |
| 107 | `rmk:choosechi` | rmk:choosechi | 3_5:1250 | example | - | - | iv | none | example (mollifier) | Def:QtPt | - |  |
| 108 | `lem_+Q` | lem_+Q, normQA | 3_5:1285 | claim | ST | both | iv | none | norm of Q_t on tensors with fast decay | lem:STOeq_Qt, [Step6-proof: proof@6:93] | Induction/QopBounds.lean:525 `Ind.qopNorm` |  |
| 109 | `lem:STOeq_Qt` | lem:STOeq_Qt, am;asoi222 | 3_5:1362 | lemma [Inductive bootstrap bound fo] | ST | both | iv | none | inductive bootstrap bound for Xi | lem:iterations, lem: newPQ, lem:STOeq_Qt_nonzero, [Step4-proof: 3_5:1602] | Induction/Step3.lean:1777 `Ind.step3` | internal by DECISIONS §5: [YY_25] Section 5.6 of@3_5:1380 |
| 110 | `lem:iterations` | lem:iterations, eq:iteration_induc | 3_5:1407 | lemma | ST | both | iv | none | iteration of the bootstrap bound | Eq:LGxb | Induction/Step3.lean:1777 `Ind.step3` | internal by DECISIONS §5: (5.109) of [YY_25] (3_5:1403) |
| 111 | `def;zero_mode_remove` | def;zero_mode_remove | 3_5:1444 | definition [Zero-mode-removing operators] | EK | both | i | Kernel/Evolution.lean:190 `noncomputable def avgOp (i : Fin n) (A : (Fin n → Zd d L) → ℂ) : (Fin n → Zd d L) → ℂ` ⟦#check: `(d L : ℕ) → [NeZero L] → {n : ℕ} → Fin n → ((Fin n → RBM.Zd d L) → ℂ) → (Fin n → RBM.Zd d L) → ℂ`⟧<br>Kernel/Evolution.lean:194 `noncomputable def zeroModeOp (i : Fin n) (A : (Fin n → Zd d L) → ℂ) : (Fin n → Zd d L) → ℂ` ⟦#check: `(d L : ℕ) → [NeZero L] → {n : ℕ} → Fin n → ((Fin n → RBM.Zd d L) → ℂ) → (Fin n → RBM.Zd d L) → ℂ`⟧<br>Kernel/Evolution.lean:199 `noncomputable def zeroModeSet (A : Finset (Fin n)) (T : (Fin n → Zd d L) → ℂ) : (Fin n → Zd d L) → ℂ` ⟦#check: `(d L : ℕ) → [NeZero L] → {n : ℕ} → Finset (Fin n) → ((Fin n → RBM.Zd d L) → ℂ) → (Fin n → RBM.Zd d L) → ℂ`⟧<br>Kernel/Evolution.lean:205 `noncomputable def projMat : Matrix (Zd d L) (Zd d L) ℂ` ⟦#check: `(d L : ℕ) → Matrix (RBM.Zd d L) (RBM.Zd d L) ℂ`⟧ | P^{(i)}, Q^{(i)}=I-P^{(i)} (projMat) and Q^{(A)}; matches the paper | [sec 3_5:1935 Step 5: Pointwise estimate for (cL], [sub 3_5:2251 The case g2/Ld leq 1-t leq 1-s leq], [Step6-proof: proof@6:93], lem:sum_decay_nonzero | none (d=2 route has no P/Q zero-mode operators) |  |
| 112 | `lem: newPQ` | lem: newPQ, yurenAL, yurenAK | 3_5:1482 | lemma | ST | both | iv | none | expansion of Q^{(A)} L and Q^{(A)} K | def;zero_mode_remove, lem:STOeq_Qt_nonzero | none |  |
| 113 | `lem:STOeq_Qt_nonzero` | lem:STOeq_Qt_nonzero | 3_5:1561 | lemma | ST | both | iv | none | bootstrap for 1-s <= lambda^2/L^2 (zero-mode removal) | Eq:LGxb, lem: newPQ, [Step4-proof: 3_5:1602] | none (d>=3 only) |  |
| 114 | `lem:sum_Ndecay` | lem:sum_Ndecay, sum_res_Ndecay | 3_5:1620 | lemma | EK | band | i | Kernel/Evolution.lean:157 `theorem norm_UN_le (hL : 3 ≤ L) {n : ℕ} {m : Fin n → ℂ} (hm : ∀ i, ‖m i‖ = 1) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) (A : (Fin n → Zd d L) → ℂ) : ‖UN d L g m s t A‖ ≤ ((1 - s) / (1 - t)) ^ n * ‖A‖`<br>Kernel/Evolution.lean:131 `theorem norm_UN_apply_le (hL : 3 ≤ L) {n : ℕ} {m : Fin n → ℂ} (hm : ∀ i, ‖m i‖ = 1) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) (A : (Fin n → Zd d L) → ℂ) (a : Fin n → Zd d L) : ‖UN d L g m s t A a‖ ≤ ((1 - s) / (1 - t)) ^ n * ‖A‖`<br>Kernel/Evolution.lean:114 `theorem norm_uKer_le (hL : 3 ≤ L) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) (hμ : ‖μ‖ = 1) : ‖uKer d L g μ s t‖ ≤ (1 - s) / (1 - t)` | \|\|U^(n)_{s,t,sigma} o A\|\|_inf <= ((1-s)/(1-t))^n \|\|A\|\|_inf; band (\|m(sigma)\|=1), 3<=L | [Step3-proof: 3_5:1435], TailtoTail, [Step6-proof: proof@6:93], [sub A:84 Proofs of evolution kernel estimat] | Path/UBounds.lean:480 `Path.sumNdecay` |  |
| 115 | `lem:sum_decay` | lem:sum_decay, deccA0, sum_res_1, sum_res_2_NAL, sumAzero, sum_res_2 | 3_5:1632 | lemma | EK | band | iv | Kernel/SumDecay.lean:667 `theorem sum_prod_norm_XiKer_le {k n : ℕ} {μ : Fin n → ℂ} (hd : 3 ≤ k + 2) (hg : 0 < g) (hμ : ∀ i, ‖μ i‖ = 1) (hdecay : ∀ i, ThetaDecay (k + 2) g (μ i)) : ∃ C > (0 : ℝ), ∀ (L : ℕ) (_ : 3 ≤ L) (s t : ℝ), 0 ≤ s → s ≤ t → t < 1 → g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t → ∀ Λ : ℝ, 1 ≤ Λ → ∀ R : ℝ, 1 ≤ R → R ≤ Λ * ellT L g s → haveI : NeZero L`<br>Kernel/SumDecay.lean:540 `theorem sum_ball_norm_XiKer_le {k : ℕ} {μ : ℂ} (hd : 3 ≤ k + 2) (hg : 0 < g) (hμ : ‖μ‖ = 1) (hdecay : ThetaDecay (k + 2) g μ) : ∃ C > (0 : ℝ), ∀ (L : ℕ) (_ : 3 ≤ L) (s t : ℝ), 0 ≤ s → s ≤ t → t < 1 → g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t → ∀ Λ : ℝ, 1 ≤ Λ → ∀ R : ℝ, 1 ≤ R → R ≤ Λ * ellT L g s → haveI : NeZero L`<br>Kernel/SumDecay.lean:376 `theorem norm_XiKer_apply_le {k : ℕ} {μ : ℂ} (hd : 3 ≤ k + 2) (hg : 0 < g) (hμ : ‖μ‖ = 1) (hdecay : ThetaDecay (k + 2) g μ) : ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∀ (L : ℕ) (_ : 3 ≤ L) (s t : ℝ), 0 ≤ s → s ≤ t → t < 1 → g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t → haveI : NeZero L`<br>Kernel/Evolution.lean:445 `theorem exists_norm_uKer_same_le {g : ℝ} {m : ℂ} (hd : 3 ≤ k + 2) (hg : 0 < g) (hm : ‖m‖ = 1) (hmi : 0 < m.im) (hshort : ThetaDecayShort (k + 2) g m) : ∃ C > (0 : ℝ), ∀ (L : ℕ) (_ : 3 ≤ L) (s t : ℝ), 0 ≤ s → s ≤ t → t < 1 → haveI : NeZero L`<br>Kernel/SumDecay.lean:348 `theorem UN_apply_eq_sum_powerset {n : ℕ} {m : Fin n → ℂ} (hL : 3 ≤ L) (hm : ∀ i, ‖m i‖ = 1) {s t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (𝒜 : (Fin n → Zd d L) → ℂ) (a : Fin n → Zd d L) : UN d L g m s t 𝒜 a = ∑ A ∈ (Finset.univ : Finset (Fin n)).powerset, ∑ b : Fin n → Zd d L, ((∏ i ∈ A, (1 : Matrix (Zd d L) (Zd d L) ℂ) (a i) (b i)) * ∏ i ∈ Finset.univ \ A, XiKer d L g (cycProd m i) s t (a i) (b i)) * 𝒜 b` | ingredients only, conditional on ThetaDecay / ThetaDecayShort for fixed g; the lemma (W^{C_n eps}, cases 1-5) absent | lem_decayLoop, lem:STOeq_NQ, Def:QtPt, lem_+Q, lem:STOeq_Qt, [Step3-proof: 3_5:1435] …(+2) | Evolution/Case3.lean:3861 `Evol.sumDecayCase3Prec`<br>Evolution/Case5.lean:1166 `Evol.ugenPairCase1Explicit` | internal by DECISIONS §5: (5.109) analogue; [YY_25] Lemma 5.7 |
| 116 | `lem:sum_decay_nonzero` | lem:sum_decay_nonzero, sum_res_Ndecay_nonzero | 3_5:1666 | lemma | EK | band | iii | Kernel/Evolution.lean:629 `theorem norm_zeroModeSet_UN_le {k n : ℕ} {g : ℝ} {m : Fin n → ℂ} {A : Finset (Fin n)} (hd : 3 ≤ k + 2) (hg : 0 < g) (hm : ∀ i, ‖m i‖ = 1) (hmi : ∀ i, 0 < (m i).im) (hshort : ∀ i, ThetaDecayShort (k + 2) g (m i)) (hzero : ∀ i, ThetaZeroMode (k + 2) g (cycProd m i)) (hA : SameSignOutside m A) {τ : ℝ} (hτ : 0 < τ) : ∃ C > (0 : ℝ), ∀ (L : ℕ) (_ : 3 ≤ L) (s t : ℝ), 0 ≤ s → s ≤ t → t < 1 → 1 - s ≤ g ^ 2 / (L : ℝ) ^ 2 → haveI : NeZero L` | unproved hypotheses ThetaDecayShort (all i), ThetaZeroMode (all cyclic products), constants depend on g; AND restriction hmi: Im m_i > 0 for ALL i, so charge - (m(-)=conj m, Im<0) is excluded (follows by conjugation, not stated); class iii = weakest of ii, iii | [Step3-proof: 3_5:1435], lem: newPQ, lem:STOeq_Qt_nonzero, [Step6-proof: proof@6:93], [sub A:84 Proofs of evolution kernel estimat] | Induction/QopBounds.lean:622 `Ind.qopDecay` — d=2: sum-zero Q_t instead |  |
| 117 | `lem;CLT` | lem;CLT, iksjuwjx3_far | 3_5:2173 | lemma | ST | both | iv | none | CLT cancellation for f^far (Step 5, 1-t in [l^2/L^2, l^2]) | (none cited; statement/definition) | Evolution/CltDecorrelation.lean:311 `Evol.cltFar`<br>Evolution/CltStep.lean:600 `Evol.cltStep`<br>Evolution/CltDecorrelation.lean:277 `Evol.CltFarThm` | internal by DECISIONS §5: [DYYY25] §7 and (7.39); [RBSO1D] App. A.10, (A.112) |
| 118 | `lem_dec_calE` | lem_dec_calE, res_deccalE_lk, res_deccalE_wG, res_deccalE_dif | 3_5:2317 | lemma | ST | both | iv | none | lem_dec_calE (1-t >= lambda^2) | TailtoTail, lem:pf_step5 | Path/LemDecCalEwG.lean:1276 `Path.lemDecCalE_wG`<br>Path/LemDecCalEdif.lean:1632 `Path.lemDecCalE_dif`<br>Path/LemDecCalE.lean:72 `Path.LemDecCalE_lk` | internal by DECISIONS §5: Lemma 5.7 of [YY_25] |
| 119 | `TailtoTail` | TailtoTail, neiwuj | 3_5:2344 | lemma | ST | both | iv | none | U kernel transports tails | lem:pf_step5 | Path/UTransport.lean:422 `Path.tailtoTail`<br>Path/UTransport.lean:170 `Path.uopLocalMax` | internal by DECISIONS §5: (2.76) analogue of [YY_25] |
| 120 | `lem:pf_step5` | lem:pf_step5 | 3_5:2376 | lemma | ST | both | iv | none | T >= t w.h.p. in Step 5 (1-t >= lambda^2) | (none cited; statement/definition) | Induction/Step45.lean:1258 `Ind.step5` | internal by DECISIONS §5: analogous to (2.76) in [YY_25] §5.3 |
| 121 | `lem:improve_exp_aver` | lem:improve_exp_aver, res_ELK_n=1 | 6:12 | lemma | ST | both | iv | none | E tr((G-M)E_a) <= (W^{-d}B)^2 | lem:LWterm_EXP, [Step6-proof: proof@6:93] | Evolution/Step61.lean:853 `Evol.step61` | internal by DECISIONS §5: Lemma 5.15 of [YY_25] |
| 122 | `lem:LWterm_EXP` | lem:LWterm_EXP, eq:ExpLWn=2 | 6:83 | lemma [Expected light-weight estima] | LW | both | iv | none | expected light-weight estimate | lem:improve_exp_aver, [Step6-proof: proof@6:93], lem_ConArg_BA | Evolution/Step61.lean:853 `Evol.step61`<br>Evolution/MLExpVocab.lean:83 `Evol.MLExpHyps` |  |
| 123 | `lem:LW_moment` | lem:LW_moment, eq:LW_moment | 7_8:72 | lemma | LW | both | iv | none | moment bound for f_xy(G); graphical expansion (Gaussian IBP) | lem:LWterm, lem: EWGn2_N, lem:LW_moment_exp, [sub 7_8:402 Examples and nested property], lem:localregular, GtoAG …(+3) | none | internal by DECISIONS §5: [yang2021delocalization], [yang2022delocalization], [yang2021random] (7_8:4, 69, 100) |
| 124 | `lem:LW_moment_exp` | lem:LW_moment_exp, eq:LW_moment_exp | 7_8:78 | lemma | LW | both | iv | none | expected T-version of lem:LW_moment | lem:LWterm, lem: EWGn2_N, lem:LW_moment, lem:LW_moment_exp_far, lem:LW_moment_exp_near, GGGamma | none | internal by DECISIONS §5: [yang2021delocalization]@7_8:100; [yang2021random]@7_8:100; other cited keys in the row region (outside the DECISIONS §2 inventory): [yang2022delocalization]@7_8:100 |
| 125 | `def_graph1` | def_graph1 | 7_8:116 | definition [Graphs] | LW | both | iv | none | graphs (vertices, solid/dotted/waved edges) | lem:LWterm, lem: EWGn2_N, ValG, def: BM2, lem:Anp_key_gh, tree-representation_BA | none | internal by DECISIONS §5: [yang2021delocalization] (7_8:127) |
| 126 | `ValG` | ValG | 7_8:159 | definition [Values of graphs] | LW | both | iv | none | value of a graph | def_auxgraph | none | internal by DECISIONS §5: [yang2021delocalization]@7_8:167; [Xu:2024aa]@7_8:167; [yang2021random]@7_8:167; other cited keys in the row region (outside the DECISIONS §2 inventory): [yang2022delocalization]@7_8:167 |
| 127 | `def_poly` | def_poly | 7_8:171 | definition [Molecules and molecular grap] | LW | both | iv | none | molecules and molecular graphs | lem:LWterm, lem: EWGn2_N, tree-representation_BA | none |  |
| 128 | `defnlvl0` | defnlvl0 | 7_8:196 | definition [Normal graphs] | LW | both | iv | none | normal graphs | (none cited; statement/definition) | none |  |
| 129 | `dot-def` | dot-def, odot | 7_8:214 | definition [Dotted edge partition] | LW | both | iv | none | dotted edge partition | lem:localregular | none |  |
| 130 | `def scaling` | def scaling, eq_defsize, eq_defsizemax | 7_8:232 | definition [Scaling size] | LW | both | iii | Graph/ScalingOrder.lean:49 `structure Counters` ⟦#check: `Type`⟧ | size(Gamma)=(L^d)^{n_M} Psi^{n_S} W^{-d(n_W-n_V)} in counters only (no graphs) | dot-def, def scaling order, GtoAG, defn_normalBA, def scalingBA | none |  |
| 131 | `def scaling order` | def scaling order, eq:ordG | 7_8:270 | definition [Scaling order] | LW | both | iii | Graph/ScalingOrder.lean:65 `def ord (c : Counters) : ℤ` ⟦#check: `RBM.Graph.Counters → ℤ`⟧<br>Graph/ScalingOrder.lean:49 `structure Counters` ⟦#check: `Type`⟧ | ord = n_S + 2(n_W - n_V) on counters (Counters -> Z); graphs absent | lem:localregular, def_auxgraph, GtoAG | none | internal by DECISIONS §5: [yang2021delocalization]@7_8:291 |
| 132 | `ssl` | ssl, Owx | 7_8:294 | lemma [Weight expansion, Lemma 3.5 ] | LW | both | iv | Graph/Expansions.lean:63 `theorem hasDerivAt_inverse_apply {A : Matrix n n ℂ} (hA : IsUnit A) (α w i j : n) : HasDerivAt (fun s : ℂ => Ring.inverse (A + s • single α w (1 : ℂ)) i j) (-(Ring.inverse A i α * Ring.inverse A w j)) 0`<br>Gauss/Stein.lean:198 `theorem integral_mul_gaussianReal_complex (hv : var ≠ 0) {f f' : ℝ → ℂ} {C : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf'c : Continuous f') (hb : ∀ x, ‖f x‖ ≤ C) (hb' : ∀ x, ‖f' x‖ ≤ C) : ∫ x : ℝ, (x : ℂ) * f x ∂(gaussianReal 0 var) = ((var : ℝ) : ℂ) * ∫ x : ℝ, f' x ∂(gaussianReal 0 var)`<br>Gauss/SteinMatrix.lean:51 `theorem integral_mul_gaussianReal_complex' {var : ℝ≥0} {f f' : ℝ → ℂ} {C : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf'c : Continuous f') (hb : ∀ x, ‖f x‖ ≤ C) (hb' : ∀ x, ‖f' x‖ ≤ C) : ∫ x : ℝ, (x : ℂ) * f x ∂(gaussianReal 0 var) = ((var : ℝ) : ℂ) * ∫ x : ℝ, f' x ∂(gaussianReal 0 var)` | weight expansion (Owx), =_E identity; ingredient only: d G_ij/dh_{aw} = -G_ia G_wj | T eq0, [sub 7_8:402 Examples and nested property], lem:localregular | none (Stein identity: Gauss/Stein*.lean) | internal by DECISIONS §5: Lemma 3.5 of [yang2021delocalization] |
| 133 | `Oe14` | Oe14, multi setting, Oe1x | 7_8:309 | lemma [Edge expansion, Lemma 3.10 o] | LW | both | iv | Graph/Expansions.lean:63 `theorem hasDerivAt_inverse_apply {A : Matrix n n ℂ} (hA : IsUnit A) (α w i j : n) : HasDerivAt (fun s : ℂ => Ring.inverse (A + s • single α w (1 : ℂ)) i j) (-(Ring.inverse A i α * Ring.inverse A w j)) 0`<br>Gauss/Stein.lean:198 `theorem integral_mul_gaussianReal_complex (hv : var ≠ 0) {f f' : ℝ → ℂ} {C : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf'c : Continuous f') (hb : ∀ x, ‖f x‖ ≤ C) (hb' : ∀ x, ‖f' x‖ ≤ C) : ∫ x : ℝ, (x : ℂ) * f x ∂(gaussianReal 0 var) = ((var : ℝ) : ℂ) * ∫ x : ℝ, f' x ∂(gaussianReal 0 var)`<br>Gauss/SteinMatrix.lean:51 `theorem integral_mul_gaussianReal_complex' {var : ℝ≥0} {f f' : ℝ → ℂ} {C : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf'c : Continuous f') (hb : ∀ x, ‖f x‖ ≤ C) (hb' : ∀ x, ‖f' x‖ ≤ C) : ∫ x : ℝ, (x : ℂ) * f x ∂(gaussianReal 0 var) = ((var : ℝ) : ℂ) * ∫ x : ℝ, f' x ∂(gaussianReal 0 var)` | edge expansion; ingredient only | lem:localregular | none | internal by DECISIONS §5: Lemma 3.10 of [yang2021delocalization] |
| 134 | `T eq0` | T eq0, Oe2x | 7_8:334 | lemma | LW | both | iv | Graph/Expansions.lean:63 `theorem hasDerivAt_inverse_apply {A : Matrix n n ℂ} (hA : IsUnit A) (α w i j : n) : HasDerivAt (fun s : ℂ => Ring.inverse (A + s • single α w (1 : ℂ)) i j) (-(Ring.inverse A i α * Ring.inverse A w j)) 0`<br>Gauss/Stein.lean:198 `theorem integral_mul_gaussianReal_complex (hv : var ≠ 0) {f f' : ℝ → ℂ} {C : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf'c : Continuous f') (hb : ∀ x, ‖f x‖ ≤ C) (hb' : ∀ x, ‖f' x‖ ≤ C) : ∫ x : ℝ, (x : ℂ) * f x ∂(gaussianReal 0 var) = ((var : ℝ) : ℂ) * ∫ x : ℝ, f' x ∂(gaussianReal 0 var)`<br>Gauss/SteinMatrix.lean:51 `theorem integral_mul_gaussianReal_complex' {var : ℝ≥0} {f f' : ℝ → ℂ} {C : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf'c : Continuous f') (hb : ∀ x, ‖f x‖ ≤ C) (hb' : ∀ x, ‖f' x‖ ≤ C) : ∫ x : ℝ, (x : ℂ) * f x ∂(gaussianReal 0 var) = ((var : ℝ) : ℂ) * ∫ x : ℝ, f' x ∂(gaussianReal 0 var)` | GG expansion; ingredient only | lem:LWterm_EXP, lem:localregular | none | internal by DECISIONS §5: Lemma 3.14 of [yang2021delocalization] |
| 135 | `deflvl1` | deflvl1, eq:neutralcharge | 7_8:367 | definition | LW | both | iv | none | locally standard graphs | T eq0, lem:localregular, GGGamma | none | internal by DECISIONS §5: [yang2021delocalization]@7_8:388 |
| 136 | `lvl1 lemma` | lvl1 lemma, expand lvl1 | 7_8:392 | lemma [Lemma 3.22 of citeyang2021de] | LW | both | iv | none | expansion into locally standard graphs | lem:LW_moment, [sub 7_8:402 Examples and nested property], lem:localregular, GGGamma | none | internal by DECISIONS §5: Lemma 3.22 of [yang2021delocalization] |
| 137 | `example:p=2` | example:p=2, eq:p=2graph, fig:p=2expansion | 7_8:505 | example | - | - | iv | none | example (p=2) | [sub 7_8:402 Examples and nested property] | - |  |
| 138 | `lem:localregular` | lem:localregular, eq:local_Gs, eq:MolVW, eq:deg_mole, eq:sizeGammamu | 7_8:786 | lemma | LW | both | iv | Graph/Model.lean:269 `theorem ord_weight_step (α w β₁ β₂ : V) {c₀ c₁ : Counters} (h : (classify α w β₁ β₂).Rel c₀ c₁) : ord c₀ + (classify α w β₁ β₂).gain ≤ ord c₁ ∧ ord c₀ + 1 ≤ ord c₁`<br>Graph/Model.lean:119 `def classify : (p : Pattern) → p.Realizable → Case` ⟦#check: `(p : RBM.Graph.Pattern) → p.Realizable → RBM.Graph.Case`⟧ | expansion of \|f_xy\|^p into locally standard graphs; only the case split / ord step on counters (Case.Rel assumed) | lem:LW_moment, lem:LW_moment_exp, deflvl1, GtoAG, lem:Anp, lem:LW_moment_exp_far …(+1) | none |  |
| 139 | `def: BM2` | def: BM2 | 7_8:863 | definition [Block-level vertices] | LW | both | iv | none | block-level vertices | def_atom | none |  |
| 140 | `eq:Gbyxi2` | eq:Gbyxi2 | 7_8:884 | claim | LW | both | iv | none | xi bounds (claim) | lem:LWterm_EXP, lem:LW_moment, lem:LW_moment_exp, lem:Anp | none |  |
| 141 | `def_auxgraph` | def_auxgraph, eq:ordGaux | 7_8:894 | definition [Auxiliary graphs] | LW | both | iv | none | auxiliary graphs | lem:LW_moment, lem:LW_moment_exp, GtoAG, lem:Anp, lem:Anp_key, lem:LW_moment_exp_far …(+1) | none |  |
| 142 | `GtoAG` | GtoAG, G_by_auxG | 7_8:907 | lemma | LW | both | iv | none | graph to auxiliary graph | lem:LWterm_EXP, lem:LW_moment, lem:LW_moment_exp, lem:Anp, lem:LW_moment_exp_near | none |  |
| 143 | `lem:Anp` | lem:Anp, eq:bddGamma_aux | 7_8:933 | lemma | LW | both | iv | none | bound on auxiliary graphs | lem:LW_moment, lem:LW_moment_exp | none |  |
| 144 | `lem:Anp_key` | lem:Anp_key, eq:Gbyxi3, eq:deg_mole_aux, adsuu_orig | 7_8:960 | lemma [Bounding nested graphs] | LW | both | iv | none | bounding nested graphs | [sub 7_8:402 Examples and nested property], lem:Anp, lem:Anp_key_gh, lem:LW_moment_exp_far, lem:LW_moment_exp_near | none | internal by DECISIONS §5: nested property of [yang2021random] |
| 145 | `lem:Anp_key_gh` | lem:Anp_key_gh, adsuu22 | 7_8:1041 | lemma | LW | both | iv | none | nested graphs with ghost edges | lem:LW_moment_exp_far | none | internal by DECISIONS §5: [yang2021random]@7_8:1400 |
| 146 | `lem:LW_moment_exp_far` | lem:LW_moment_exp_far, eq:LW_moment_exp_far | 7_8:1615 | lemma | LW | both | iv | none | far part of lem:LW_moment_exp | lem:LW_moment_exp_near | none |  |
| 147 | `lem:LW_moment_exp_near` | lem:LW_moment_exp_near, eq:LW_moment_exp_near | 7_8:1621 | lemma | LW | both | iv | none | near part of lem:LW_moment_exp | (none cited; statement/definition) | none |  |
| 148 | `claim:TTk` | claim:TTk, eq:key_T_reudce | 7_8:1661 | claim | EK | both | i | Kernel/PropT.lean:913 `theorem key_T_reduce (hW : 0 < W) {k n : ℕ} (hn : 2 ≤ n) {ℓ : ℝ} (hℓ : 1 ≤ ℓ) (D : Finset (Zd (k + 2) L)) (a : Zd (k + 2) L) (hD : ∀ α ∈ D, ((zdistD (k + 2) L (a - α) : ℕ) : ℝ) ≤ ℓ) (x y : Fin n → Zd (k + 2) L) : ∑ α ∈ D, ∏ i, (sfT (k + 2) L W g t (min ((zdistD (k + 2) L (x i - α) : ℕ) : ℝ) ℓ) * sfT (k + 2) L W g t (min ((zdistD (k + 2) L (y i - α) : ℕ) : ℝ) ℓ)) ≤ keyC k n * (PsiT (k + 2) L W g t ^ 2 * ℓ ^ 2) * (PsiT (k + 2) L W g t ^ (n - 2) * ∏ i, sfT (k + 2) L W g t (min ((zdistD (k + 2) L (x i - y i) : ℕ) : ℝ)  …[cut at 520 chars]`<br>Kernel/PropT.lean:1056 `theorem key_T_reduce_absorbed {L : ℕ} [NeZero L] {W g t : ℝ} (hW : 0 < W) {k n : ℕ} (hn : 2 ≤ n) {ℓ Λ : ℝ} (hℓ : 1 ≤ ℓ) (hL : 1 ≤ (L : ℝ)) (hg : 0 ≤ g) (ht : t < 1) (hgL : g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - t)) (hℓt : ℓ ≤ Λ * ellT L g t) (D : Finset (Zd (k + 2) L)) (a : Zd (k + 2) L) (hD : ∀ α ∈ D, ((zdistD (k + 2) L (a - α) : ℕ) : ℝ) ≤ ℓ) (x y : Fin n → Zd (k + 2) L) : ∑ α ∈ D, ∏ i, (sfT (k + 2) L W g t (min ((zdistD (k + 2) L (x i - α) : ℕ) : ℝ) ℓ) * sfT (k + 2) L W g t (min ((zdistD (k + 2) L (y i - α) : ℕ) : ℝ) ℓ)) ≤ k …[cut at 520 chars]`<br>Kernel/PropT.lean:469 `noncomputable def sfT (r : ℝ) : ℝ` ⟦#check: `ℕ → ℕ → ℝ → ℝ → ℝ → ℝ → ℝ`⟧<br>Kernel/PropT.lean:465 `noncomputable def PsiT : ℝ` ⟦#check: `ℕ → ℕ → ℝ → ℝ → ℝ → ℝ`⟧ | explicit-constant deterministic form, ell >= 1 (D15); l_t-scale hypothesis ell <= Lambda ell_t and g^2 <= L^2(1-t) | lem:LW_moment_exp_near | none (d=2: lem:propT sums only) |  |
| 149 | `zztE_BA` | zztE_BA, eq:t0E0_BA, eq:zztE_BA | 7_8:1796 | lemma [Lemma 3.3 of citeRBSO1D] | BA | BA | iv | none | flow reparametrization for BA (t0, E, g0=sqrt(t0) g); statement says \|Re z\|<=2-kappa, inconsistent with D_{kappa,eps}^{BA} | MR:decol_BA, def_Theta, eq:spectral_domainBA, lem:main_ind_BA, lem:propM, lem_ConArg_BA | none | internal by DECISIONS §5: Lemma 3.3 of [RBSO1D] |
| 150 | `eq:spectral_domainBA` | eq:spectral_domainBA | 7_8:1817 | eq/def | BA | BA | iv | none | D^{BA}_{kappa,eps}: \|E\| <= e_g - kappa | (none cited; statement/definition) | none |  |
| 151 | `lem:main_ind_BA` | lem:main_ind_BA | 7_8:1825 | theorem | BA | BA | iv | none | inductive step for BA | MR:decol_BA, lem:propM, lem_GbEXP_BA, lem_ConArg_BA | none | internal by DECISIONS §5: [RBSO1D] §7.1 |
| 152 | `lem:propM` | lem:propM, eq:WardM, Mbound_AO, Mbound_AO2 | 7_8:1846 | lemma | BA | BA | iv | none | properties of m, M^(B): translation invariance, Ward, Combes-Thomas | ML:Kbound, lem_propTH, lem: EMn2_N, lem:LW_moment, lem:LW_moment_exp, lem_GbEXP_BA …(+6) | RBM2D has Combes-Thomas files (Propagator/CombesThomas*), object differs | internal by DECISIONS §5: [LeeSchSteYau2015] Lemma 3.5; [Aizenman_book] Thm 10.5 |
| 153 | `lem_GbEXP_BA` | lem_GbEXP_BA, eq:def_Psit, GiiGEX_BA, GijGEX_BA | 7_8:1916 | lemma | BA | BA | iv | none | BA version of lem_GbEXP | lem: EMn2_N, lem:LW_moment, lem:LW_moment_exp, lem_ConArg_BA | none | internal by DECISIONS §5: [RBSO1D] Lemma 6.1 |
| 154 | `lem_ConArg_BA` | lem_ConArg_BA, res_lo_bo_eta_BA, eq:ImGs, eq:ImGt | 7_8:1956 | lemma | BA | BA | iv | none | BA version of lem_ConArg | lem_GbEXP_BA | none | internal by DECISIONS §5: [YY_25]@7_8:2101; Lemma 7.1 of [RBSO1D] |
| 155 | `def:canpnical_part` | def:canpnical_part | A:321 | definition [Canonical partitions] | KL | both | iii | Loop/Partition.lean:91 `def TSP (n : ℕ) : Finset (Finset (Fin n × Fin n))` ⟦#check: `(n : ℕ) → Finset (Finset (Fin n × Fin n))`⟧<br>Loop/Partition.lean:65 `def IsDiag (n : ℕ) (i j : Fin n) : Prop` ⟦#check: `(n : ℕ) → Fin n → Fin n → Prop`⟧<br>Loop/Partition.lean:77 `def Crossing {n : ℕ} (e f : Fin n × Fin n) : Prop` ⟦#check: `{n : ℕ} → Fin n × Fin n → Fin n × Fin n → Prop`⟧<br>Loop/Partition.lean:84 `def CrossingFree {n : ℕ} (F : Finset (Fin n × Fin n)) : Prop` ⟦#check: `{n : ℕ} → Finset (Fin n × Fin n) → Prop`⟧<br>Loop/Partition.lean:72 `def diagonals (n : ℕ) : Finset (Fin n × Fin n)` ⟦#check: `(n : ℕ) → Finset (Fin n × Fin n)`⟧ | reformulation: TSP n = sets of non-crossing diagonals of an n-gon (tree leaves = vertices); equivalence with the polygon-region definition of the paper is not stated on main | tree-representation | Loop/Kcal.lean:66 `KLoop.TSP`<br>Loop/Kcal.lean:40 `KLoop.IsDiag`<br>Loop/Kcal.lean:51 `KLoop.Crossing` | internal by DECISIONS §5: [RBSO1D]@A:335; [YY_25] (Section 3 definitions) |
| 156 | `f-external` | f-external, f-internal, M-graph-value-unsummed | A:340 | definition | KL | band | iii | Loop/Partition.lean:166 `noncomputable def thetaEdge (m : Bool → ℂ) (t : ℝ) (s s' : Bool) : Matrix (Zd d L) (Zd d L) ℂ` ⟦#check: `(d L : ℕ) → [NeZero L] → ℝ → (Bool → ℂ) → ℝ → Bool → Bool → Matrix (RBM.Zd d L) (RBM.Zd d L) ℂ`⟧<br>Loop/Partition.lean:223 `noncomputable def treeVal (m : Bool → ℂ) (t : ℝ) (σ : List Bool) (a : List (Zd d L)) (F : List (ℕ × ℕ)) : ℂ` ⟦#check: `(d L : ℕ) → [NeZero L] → ℝ → (Bool → ℂ) → ℝ → List Bool → List (RBM.Zd d L) → List (ℕ × ℕ) → ℂ`⟧<br>Loop/Partition.lean:239 `noncomputable def GammaN {n : ℕ} (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool) (a : Fin n → Zd d L) (F : Finset (Fin n × Fin n)) : ℂ` ⟦#check: `(d L : ℕ) → [NeZero L] → ℝ → {n : ℕ} → (Bool → ℂ) → ℝ → (Fin n → Bool) → (Fin n → RBM.Zd d L) → Finset (Fin n × Fin n) → ℂ`⟧<br>Loop/Partition.lean:246 `noncomputable def GammaSum {n : ℕ} (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool) (a : Fin n → Zd d L) : ℂ` ⟦#check: `(d L : ℕ) → [NeZero L] → ℝ → {n : ℕ} → (Bool → ℂ) → ℝ → (Fin n → Bool) → (Fin n → RBM.Zd d L) → ℂ`⟧ | edge values f_{t,sigma}(e) via Theta; band only (BA g_{t,sigma} of M-graph-value-definition absent) | M-graph-value-definition | Loop/Kcal.lean:203 `KLoop.Kcal` | internal by DECISIONS §5: [YY_25] Lemma 3.4 of@A:366 |
| 157 | `tree-representation#n<=3` | tree-representation, eq_Ktree | A:368 | lemma [Lemma 3.4 of citeYY25] | KL | band | ii | Loop/TreeThree.lean:350 `theorem kThree_eq_of_isKLoop (hL : 3 ≤ L) (hW : (W : ℂ) ^ d ≠ 0) {m : Bool → ℂ} (hm : ∀ s, ‖m s‖ = 1) {K : ℝ → LoopIdx (Zd d L) → ℂ} (hK : IsKLoop d L W g m (Set.Ico 0 1) K) (hbdd : TwoLoopBounded d L K) : ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ₀ σ₁ σ₂ : Bool) (a₀ a₁ a₂ : Zd d L), K t ⟨[σ₀, σ₁, σ₂], [a₀, a₁, a₂]⟩ = kThree d L W g m t σ₀ σ₁ σ₂ a₀ a₁ a₂`<br>Loop/TreeThree.lean:91 `theorem treeSum_three (m : Bool → ℂ) (t : ℝ) (σ₀ σ₁ σ₂ : Bool) (a₀ a₁ a₂ : Zd d L) : treeSum d L g m t [σ₀, σ₁, σ₂] [a₀, a₁, a₂] = ∑ b : Zd d L, thetaEdge d L g m t σ₀ σ₁ a₀ b * thetaEdge d L g m t σ₁ σ₂ a₁ b * thetaEdge d L g m t σ₂ σ₀ a₂ b`<br>Loop/TreeThree.lean:411 `theorem pureLoop_three {k : ℕ} {m : Bool → ℂ} {K : ℝ → LoopIdx (Zd (k + 2) L) → ℂ} (hd : 3 ≤ k + 2) (hg : 0 < g) (hL : 3 ≤ L) (hW : (W : ℂ) ^ (k + 2) ≠ 0) {σ : Bool} (hm : ∀ s, ‖m s‖ = 1) (hmi : 0 < (m σ).im) (hshort : ThetaDecayShort (k + 2) g (m σ)) (hK : IsKLoop (k + 2) L W g m (Set.Ico 0 1) K) (hbdd : TwoLoopBounded (k + 2) L K) : ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∀ (t : ℝ), 0 ≤ t → t < 1 → ∀ (a : Fin 3 → Zd (k + 2) L) (p q : Fin 3), ‖K t ⟨[σ, σ, σ], [a 0, a 1, a 2]⟩‖ ≤ C * ‖(((W : ℂ) ^ (k + 2))⁻¹) ^ 2‖ * Real.exp  …[cut at 520 chars]` | n=3: K^(3) = tree sum, proved for every family of K-loops with the a priori 2-loop bound (TwoLoopBounded) | ML:Kbound, M-graph-value-definition | Loop/TreeRep.lean:2563 `KLoop.isPrimitive_Kcal` | internal by DECISIONS §5: [RBSO1D]@A:376; Lemma 3.4 of [YY_25] |
| 158 | `tree-representation#n>=4` | tree-representation, eq_Ktree | A:368 | lemma [Lemma 3.4 of citeYY25] | KL | band | iv | Loop/TreeRep.lean:182 `def KTreeRep (m : Bool → ℂ) (K : ℝ → LoopIdx (Zd d L) → ℂ) : Prop` ⟦#check: `(d L : ℕ) → [NeZero L] → ℕ → ℝ → (Bool → ℂ) → (ℝ → RBM.Loop.LoopIdx (RBM.Zd d L) → ℂ) → Prop`⟧<br>Loop/TreeFour.lean:134 `theorem treeSum_four (m : Bool → ℂ) (t : ℝ) (σ₀ σ₁ σ₂ σ₃ : Bool) (a₀ a₁ a₂ a₃ : Zd d L) : treeSum d L g m t [σ₀, σ₁, σ₂, σ₃] [a₀, a₁, a₂, a₃] = treeVal d L g m t [σ₀, σ₁, σ₂, σ₃] [a₀, a₁, a₂, a₃] [] + treeVal d L g m t [σ₀, σ₁, σ₂, σ₃] [a₀, a₁, a₂, a₃] [(0, 2)] + treeVal d L g m t [σ₀, σ₁, σ₂, σ₃] [a₀, a₁, a₂, a₃] [(1, 3)]`<br>Loop/Partition.lean:277 `theorem GammaSum_eq_sum {n : ℕ} (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool) (a : Fin n → Zd d L) : GammaSum d L g m t σ a = ∑ F ∈ TSP n, GammaN d L g m t σ a F` | only the Prop KTreeRep (borrowed); n=4 tree-side computations (treeSum_four) but no solution statement | ML:Kbound, M-graph-value-definition | Loop/TreeRep.lean:2563 `KLoop.isPrimitive_Kcal` | internal by DECISIONS §5: [RBSO1D]@A:376; Lemma 3.4 of [YY_25] (internal by DECISIONS 5) |
| 159 | `m-loop-tsp` | m-loop-tsp, b_i-subgraph, eq:M-loopexample, Fig:Mloop | A:380 | definition [Canonical partitions with M-] | BA | BA | iv | none | canonical partitions with M-loops | M-graph-value-definition | none | internal by DECISIONS §5: [RBSO1D] §4 |
| 160 | `M-graph-value-definition` | M-graph-value-definition, f-external2, f-internal2, eq:Mloop_defgen, M-graph-value-unsummed2 | A:552 | definition | BA | BA | iv | none | values of M-graphs | (none cited; statement/definition) | none | internal by DECISIONS §5: [RBSO1D] §4 |
| 161 | `tree-representation_BA` | tree-representation_BA, eq:tree_rep2 | A:592 | lemma [Lemma 4.16 of citeRBSO1D] | BA | BA | iv | none | tree representation for BA | lem_pureloop | none | internal by DECISIONS §5: [YY_25] Section 3.3 of@A:602; Lemma 4.16 of [RBSO1D] |
| 162 | `lem_pureloop#n<=3` | lem_pureloop, res_pureKes | A:643 | lemma | KL | band | iii | Loop/PureLoop.lean:254 `theorem pureLoop_two {k : ℕ} {m : Bool → ℂ} {K : ℝ → LoopIdx (Zd (k + 2) L) → ℂ} (hd : 3 ≤ k + 2) (hg : 0 < g) (hL : 3 ≤ L) {σ : Bool} (hm : ‖m σ‖ = 1) (hmi : 0 < (m σ).im) (hshort : ThetaDecayShort (k + 2) g (m σ)) (hK : KTwoFormula (k + 2) L W g m K) : ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∀ (t : ℝ), 0 ≤ t → t < 1 → ∀ a₁ a₂ : Zd (k + 2) L, ‖K t ⟨[σ, σ], [a₁, a₂]⟩‖ ≤ C * ‖((W : ℂ) ^ (k + 2))⁻¹‖ * Real.exp (-(c * (zdistD (k + 2) L (a₁ - a₂) : ℝ)))`<br>Loop/TreeThree.lean:411 `theorem pureLoop_three {k : ℕ} {m : Bool → ℂ} {K : ℝ → LoopIdx (Zd (k + 2) L) → ℂ} (hd : 3 ≤ k + 2) (hg : 0 < g) (hL : 3 ≤ L) (hW : (W : ℂ) ^ (k + 2) ≠ 0) {σ : Bool} (hm : ∀ s, ‖m s‖ = 1) (hmi : 0 < (m σ).im) (hshort : ThetaDecayShort (k + 2) g (m σ)) (hK : IsKLoop (k + 2) L W g m (Set.Ico 0 1) K) (hbdd : TwoLoopBounded (k + 2) L K) : ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∀ (t : ℝ), 0 ≤ t → t < 1 → ∀ (a : Fin 3 → Zd (k + 2) L) (p q : Fin 3), ‖K t ⟨[σ, σ, σ], [a 0, a 1, a 2]⟩‖ ≤ C * ‖(((W : ℂ) ^ (k + 2))⁻¹) ^ 2‖ * Real.exp  …[cut at 520 chars]`<br>Loop/Unique.lean:344 `theorem pureLoop_two_of_isKLoop {k : ℕ} (hd : 3 ≤ k + 2) (hg : 0 < g) (hL : 3 ≤ L) (hW : (W : ℂ) ^ (k + 2) ≠ 0) {m : Bool → ℂ} (hm : ∀ s, ‖m s‖ = 1) {σ : Bool} (hmi : 0 < (m σ).im) (hshort : ThetaDecayShort (k + 2) g (m σ)) {K : ℝ → LoopIdx (Zd (k + 2) L) → ℂ} (hK : IsKLoop (k + 2) L W g m (Set.Ico 0 1) K) (hbdd : TwoLoopBounded (k + 2) L K) : ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∀ (t : ℝ), 0 ≤ t → t < 1 → ∀ a₁ a₂ : Zd (k + 2) L, ‖K t ⟨[σ, σ], [a₁, a₂]⟩‖ ≤ C * ‖((W : ℂ) ^ (k + 2))⁻¹‖ * Real.exp (-(c * (zdistD (k + 2) L (a …[cut at 520 chars]`<br>Loop/Primitive.lean:150 `theorem pureLoop_two_kTwoLoop {k : ℕ} {m : Bool → ℂ} (hd : 3 ≤ k + 2) (hg : 0 < g) (hL : 3 ≤ L) {σ : Bool} (hm : ‖m σ‖ = 1) (hmi : 0 < (m σ).im) (hshort : ThetaDecayShort (k + 2) g (m σ)) : ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∀ (t : ℝ), 0 ≤ t → t < 1 → ∀ a₁ a₂ : Zd (k + 2) L, ‖kTwoLoop (k + 2) L W g m t ⟨[σ, σ], [a₁, a₂]⟩‖ ≤ C * ‖((W : ℂ) ^ (k + 2))⁻¹‖ * Real.exp (-(c * (zdistD (k + 2) L (a₁ - a₂) : ℝ)))` | n=2,3 only; unproved hypotheses ThetaDecayShort (g,m fixed), TwoLoopBounded (general K); restriction hmi: 0 < Im m(sigma) so only the + charge (m(-) = conj m is excluded, not stated); constants depend on g; class iii = weakest of ii, iii | ML:Kbound | Loop/PureLoop.lean:793 `KLoop.Kcal_pure_prec` | internal by DECISIONS §5: [YY_25] (pure loop) |
| 163 | `lem_pureloop#n>=4` | lem_pureloop, res_pureKes | A:643 | lemma | KL | band | iv | none | general n absent | ML:Kbound | Loop/PureLoop.lean:793 `KLoop.Kcal_pure_prec` | internal by DECISIONS §5: [YY_25]@A:661 |
| 164 | `strat_local` | strat_local, eq:smallsize | B:135 | strategy [Local expansion strategy] | LW | both | iv | none | local expansion strategy | lem:localregular | none |  |
| 165 | `def_atom` | def_atom | B:302 | definition [Atoms and atomic graphs] | BA | BA | iv | none | atoms and atomic graphs (BA) | (none cited; statement/definition) | none |  |
| 166 | `defn_normalBA` | defn_normalBA | B:329 | definition [Normal graphs] | BA | BA | iv | none | normal graphs (BA) | (none cited; statement/definition) | none |  |
| 167 | `def scalingBA` | def scalingBA, eq_defsize_BA, eq:ordG_BA | B:345 | definition [Scaling size and scaling ord] | BA | BA | iii | Graph/ScalingOrder.lean:49 `structure Counters` ⟦#check: `Type`⟧<br>Graph/ScalingOrder.lean:65 `def ord (c : Counters) : ℤ` ⟦#check: `RBM.Graph.Counters → ℤ`⟧<br>Graph/ScalingOrder.lean:76 `theorem ord_case_ii {c₀ c₁ : Counters} (hW : c₁.nW = c₀.nW + 1) (hV : c₁.nV + 1 ≤ c₀.nV) (hS : c₀.nS ≤ c₁.nS + 1) : ord c₀ + 3 ≤ ord c₁`<br>Graph/ScalingOrder.lean:106 `theorem ord_case_vi {c₀ c₁ : Counters} (hW : c₁.nW = c₀.nW + 1) (hV : c₁.nV = c₀.nV) (hS : c₀.nS ≤ c₁.nS) : ord c₀ + 2 ≤ ord c₁` | scaling order on counters, cases (ii)-(vi) arithmetic only; graphs absent | (none cited; statement/definition) | none | internal by DECISIONS §5: [yang2024Del]@B:357 |
| 168 | `lanlw` | lanlw, eq:BE | B:359 | lemma [Basic expansion, Lemma B.9 o] | BA | BA | iv | Graph/Expansions.lean:63 `theorem hasDerivAt_inverse_apply {A : Matrix n n ℂ} (hA : IsUnit A) (α w i j : n) : HasDerivAt (fun s : ℂ => Ring.inverse (A + s • single α w (1 : ℂ)) i j) (-(Ring.inverse A i α * Ring.inverse A w j)) 0`<br>Gauss/Stein.lean:198 `theorem integral_mul_gaussianReal_complex (hv : var ≠ 0) {f f' : ℝ → ℂ} {C : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf'c : Continuous f') (hb : ∀ x, ‖f x‖ ≤ C) (hb' : ∀ x, ‖f' x‖ ≤ C) : ∫ x : ℝ, (x : ℂ) * f x ∂(gaussianReal 0 var) = ((var : ℝ) : ℂ) * ∫ x : ℝ, f' x ∂(gaussianReal 0 var)`<br>Gauss/SteinMatrix.lean:51 `theorem integral_mul_gaussianReal_complex' {var : ℝ≥0} {f f' : ℝ → ℂ} {C : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf'c : Continuous f') (hb : ∀ x, ‖f x‖ ≤ C) (hb' : ∀ x, ‖f' x‖ ≤ C) : ∫ x : ℝ, (x : ℂ) * f x ∂(gaussianReal 0 var) = ((var : ℝ) : ℂ) * ∫ x : ℝ, f' x ∂(gaussianReal 0 var)` | basic expansion (BA); ingredient only | (none cited; statement/definition) | none | internal by DECISIONS §5: Lemma B.9 of [yang2024Del] |
| 169 | `lem_lweight` | lem_lweight, eq:LW | B:376 | lemma | BA | BA | iv | Graph/Expansions.lean:63 `theorem hasDerivAt_inverse_apply {A : Matrix n n ℂ} (hA : IsUnit A) (α w i j : n) : HasDerivAt (fun s : ℂ => Ring.inverse (A + s • single α w (1 : ℂ)) i j) (-(Ring.inverse A i α * Ring.inverse A w j)) 0`<br>Gauss/Stein.lean:198 `theorem integral_mul_gaussianReal_complex (hv : var ≠ 0) {f f' : ℝ → ℂ} {C : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf'c : Continuous f') (hb : ∀ x, ‖f x‖ ≤ C) (hb' : ∀ x, ‖f' x‖ ≤ C) : ∫ x : ℝ, (x : ℂ) * f x ∂(gaussianReal 0 var) = ((var : ℝ) : ℂ) * ∫ x : ℝ, f' x ∂(gaussianReal 0 var)`<br>Gauss/SteinMatrix.lean:51 `theorem integral_mul_gaussianReal_complex' {var : ℝ≥0} {f f' : ℝ → ℂ} {C : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf'c : Continuous f') (hb : ∀ x, ‖f x‖ ≤ C) (hb' : ∀ x, ‖f' x‖ ≤ C) : ∫ x : ℝ, (x : ℂ) * f x ∂(gaussianReal 0 var) = ((var : ℝ) : ℂ) * ∫ x : ℝ, f' x ∂(gaussianReal 0 var)` | weight expansion (BA); ingredient only | (none cited; statement/definition) | none | internal by DECISIONS §5: Lemma B.10 of [yang2024Del] |
| 170 | `GGGamma` | GGGamma | B:393 | lemma [GG expansion, Lemma B.11 of ] | BA | BA | iv | Graph/Expansions.lean:63 `theorem hasDerivAt_inverse_apply {A : Matrix n n ℂ} (hA : IsUnit A) (α w i j : n) : HasDerivAt (fun s : ℂ => Ring.inverse (A + s • single α w (1 : ℂ)) i j) (-(Ring.inverse A i α * Ring.inverse A w j)) 0`<br>Gauss/Stein.lean:198 `theorem integral_mul_gaussianReal_complex (hv : var ≠ 0) {f f' : ℝ → ℂ} {C : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf'c : Continuous f') (hb : ∀ x, ‖f x‖ ≤ C) (hb' : ∀ x, ‖f' x‖ ≤ C) : ∫ x : ℝ, (x : ℂ) * f x ∂(gaussianReal 0 var) = ((var : ℝ) : ℂ) * ∫ x : ℝ, f' x ∂(gaussianReal 0 var)`<br>Gauss/SteinMatrix.lean:51 `theorem integral_mul_gaussianReal_complex' {var : ℝ≥0} {f f' : ℝ → ℂ} {C : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf'c : Continuous f') (hb : ∀ x, ‖f x‖ ≤ C) (hb' : ∀ x, ‖f' x‖ ≤ C) : ∫ x : ℝ, (x : ℂ) * f x ∂(gaussianReal 0 var) = ((var : ℝ) : ℂ) * ∫ x : ℝ, f' x ∂(gaussianReal 0 var)` | GG expansion (BA); ingredient only | lem:LWterm_EXP | none | internal by DECISIONS §5: Lemma B.11 of [yang2024Del] |
| 171 | `[net]` |  | 1_2:1228 and 1400 | no label | MA | both | iii | Gauss/Domination.lean:333 `theorem stochDom_Icc_of_lipschitz {T : ℝ} (hT : 0 < T) {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) {Y : ∀ _ : ℕ, ℝ → Ω → ℝ} {Φ : ℕ → ℝ} (hΦ : ∀ N, 0 < Φ N) (hΦlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Φ N) (hLip : ∀ (N : ℕ) (ω : Ω), ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ u' ∈ Set.Icc (0 : ℝ) T, \|Y N u ω - Y N u' ω\| ≤ (N : ℝ) ^ K * \|u - u'\|) (hint : ∀ (p N : ℕ) (u : ℝ), Integrable (fun ω => \|Y N u ω\| ^ (2 * p)) P) (hmom : MomentDom P (U := fun _ => ↥(Set.Icc (0 : ℝ) T)) (fun N u ω => Y N (u : ℝ) ω) (fun N _ => Φ N)) : StochDom P (U :=  …[cut at 520 chars]`<br>Gauss/Domination.lean:238 `theorem stochDom_Icc_of_holder {T : ℝ} (hT : 0 < T) {K B γ : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) (hγ : 0 < γ) {Y : ∀ _ : ℕ, ℝ → Ω → ℝ} {Φ : ℕ → ℝ} (hΦ : ∀ N, 0 < Φ N) (hΦlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Φ N) (hHol : ∀ (N : ℕ) (ω : Ω), ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ u' ∈ Set.Icc (0 : ℝ) T, \|Y N u ω - Y N u' ω\| ≤ (N : ℝ) ^ K * \|u - u'\| ^ γ) (hint : ∀ (p N : ℕ) (u : ℝ), Integrable (fun ω => \|Y N u ω\| ^ (2 * p)) P) (hmom : MomentDom P (U := fun _ => ↥(Set.Icc (0 : ℝ) T)) (fun N u ω => Y N (u : ℝ) ω) (fun N _ => Φ N)) : S …[cut at 520 chars]`<br>Gauss/Domination.lean:195 `theorem card_net_le {A : ℝ} (hA : 0 ≤ A) : ∀ᶠ N : ℕ in atTop, (Fintype.card (Fin (netSize A N + 1)) : ℝ) ≤ (N : ℝ) ^ (A + 1)`<br>Gauss/Domination.lean:79 `theorem stochDom_of_momentDom {U : ℕ → Type*} [∀ N, Fintype (U N)] {Ccard : ℝ} (hcard : ∀ᶠ N : ℕ in atTop, (Fintype.card (U N) : ℝ) ≤ (N : ℝ) ^ Ccard) {Y : ∀ N, U N → Ω → ℝ} {Φ : ∀ N, U N → ℝ} (hΦ : ∀ N u, 0 < Φ N u) (hint : ∀ (p N : ℕ) (u : U N), Integrable (fun ω => \|Y N u ω\| ^ (2 * p)) P) (hmom : MomentDom P Y Φ) : StochDom P Y (fun N u _ => Φ N u)` | "standard N^{-C}-net and perturbation argument" (uniformity in z resp. u of every estimate, and of eq:ukx for decol): main has the net lemma for ONE real parameter u in [0,T] under a Lipschitz/Holder envelope, not for z in the 2-dim domain D_{kappa,eps} | (none cited) | Main/RegionUnif.lean:815 `Endpoints.RegionUnifOfPT`<br>Main/RegionUnif.lean:824 `Endpoints.regionUnifOfPT`<br>Induction/Region.lean:55 `Ind.regionOfSequences` |  |
| 172 | `[Thm2.4-proof]` |  | 1_2:566-581 | no label | UN | band | iv | none | proof of Thm 2.4: Green-function comparison [Xu:2024aa] with the modified bad event B(y) (window N^{-1} W^{d/3}, \|M_{y,alpha}\| >= W^{-d/6}) and QUE at eps0=d/3, c=d/6; external input LSY Thm 2.2 | (none cited) | Universality/UnivMain.lean:449 `Univ.univMainRow`<br>Universality/GreenCorr.lean:730 `Univ.greenCorrAll`<br>Main/BUnivHolds.lean:32 `Endpoints.bUniv_holds` | internal by DECISIONS §5: [Xu:2024aa] (1_2:568); [DYYY25] Thm 2.6 (1_2:569); external (authorized): LSY Thm 2.2 |

## Part B: every other `\label` of the TeX (one label per line)

Labels that are neither the label of a Part A row nor a sub-label listed in its `labels in row` cell: displayed equations inside proofs, section labels, figure labels.  `inside` is the nearest enclosing Part A row or section node (script).

| label | TeX file:line | kind | inside |
|---|---|---|---|
| `Anderson_orig` | 1_2:5 | equation/figure label | [sec 1_2:1 Introduction] |
| `eqn:transition exponents` | 1_2:15 | equation/figure label | [sec 1_2:1 Introduction] |
| `eq:variance-profile` | 1_2:32 | equation/figure label | [sec 1_2:1 Introduction] |
| `eq:nGloops` | 1_2:78 | equation/figure label | [sec 1_2:1 Introduction] |
| `eq:introloop_hier` | 1_2:85 | equation/figure label | [sec 1_2:1 Introduction] |
| `eq:introLWtermS` | 1_2:91 | equation/figure label | [sec 1_2:1 Introduction] |
| `eq:diamond` | 1_2:99 | equation/figure label | [sec 1_2:1 Introduction] |
| `eq:Knequation` | 1_2:117 | equation/figure label | [sec 1_2:1 Introduction] |
| `eq:Ward_intro1` | 1_2:146 | equation/figure label | [sec 1_2:1 Introduction] |
| `eq:n=2approx` | 1_2:156 | equation/figure label | [sec 1_2:1 Introduction] |
| `eq:aprioriG2` | 1_2:175 | equation/figure label | [sec 1_2:1 Introduction] |
| `eq:introGc` | 1_2:184 | equation/figure label | [sec 1_2:1 Introduction] |
| `sec_model-results` | 1_2:250 | section label | [sec 1_2:250 The model and main results] |
| `subsec:main` | 1_2:291 | section label | [sub 1_2:291 Main results for the random band m] |
| `sec:main_BA` | 1_2:600 | equation/figure label | [sub 1_2:599 Main results for the block Anderso] |
| `sec:tools` | 1_2:681 | section label | [sub 1_2:681 Stochastic flow and loop hierarchy] |
| `Sec:Steps12` | 3_5:1 | section label | [sec 3_5:1 Steps 1 and 2: A priori G-loop est] |
| `subsec:DyLK` | 3_5:69 | section label | [sub 3_5:69 Dynamics of (cal L-cal K)-loops] |
| `subsec:step2_pf` | 3_5:302 | section label | [Step2-proof: 3_5:302] |
| `eq:kn2sol_decay` | 3_5:456 | equation/figure label | [Step2-proof: proof@3_5:454] |
| `eq:L2_decay` | 3_5:460 | equation/figure label | [Step2-proof: proof@3_5:454] |
| `lokis2` | 3_5:466 | equation/figure label | [Step2-proof: proof@3_5:454] |
| `l>0EQ` | 3_5:474 | equation/figure label | [Step2-proof: proof@3_5:454] |
| `eq:Gronwall_2L_max` | 3_5:481 | equation/figure label | [Step2-proof: proof@3_5:454] |
| `eq:L-K2max` | 3_5:504 | equation/figure label | [Step2-proof: proof@3_5:454] |
| `ksjjuw` | 3_5:513 | equation/figure label | [Step2-proof: proof@3_5:454] |
| `kwr3juw` | 3_5:521 | equation/figure label | [Step2-proof: proof@3_5:454] |
| `eq:monotone_Ku` | 3_5:525 | equation/figure label | [Step2-proof: proof@3_5:454] |
| `eq:boundGcterm` | 3_5:538 | equation/figure label | [Step2-proof: proof@3_5:454] |
| `eq:boundmgterm` | 3_5:542 | equation/figure label | [Step2-proof: proof@3_5:454] |
| `LKu2p2mmvj` | 3_5:549 | equation/figure label | [Step2-proof: proof@3_5:454] |
| `eq:def_ell1` | 3_5:571 | equation/figure label | [Step2-proof: proof@3_5:454] |
| `subsec:pf_lem:newKLK` | 3_5:610 | section label | lem:newKLK |
| `uwu3po2[]` | 3_5:613 | equation/figure label | lem:newKLK |
| `uu2j2ois` | 3_5:618 | equation/figure label | lem:newKLK |
| `eq;facts` | 3_5:622 | equation/figure label | lem:newKLK |
| `i2kk2zgg` | 3_5:628 | equation/figure label | lem:newKLK |
| `eq:i2kk2zgglast` | 3_5:652 | equation/figure label | lem:newKLK |
| `subsec:pf_lem: EMn2_N` | 3_5:669 | section label | lem: EMn2_N |
| `eq_mart-sum` | 3_5:673 | equation/figure label | lem: EMn2_N |
| `eq:2martingale_quad` | 3_5:677 | equation/figure label | lem: EMn2_N |
| `eq_6loop_quadform` | 3_5:776 | equation/figure label | ygdhmsgq0 |
| `eq:L4loop` | 3_5:780 | equation/figure label | ygdhmsgq0 |
| `eq_sym_loop_bound_old` | 3_5:788 | equation/figure label | ygdhmsgq0 |
| `eq:S1+S2` | 3_5:801 | equation/figure label | ygdhmsgq0 |
| `eq:pointwise_loop` | 3_5:812 | equation/figure label | ygdhmsgq0 |
| `eq:reduce4to3` | 3_5:816 | equation/figure label | ygdhmsgq0 |
| `eq:reduce4_bdd3` | 3_5:823 | equation/figure label | ygdhmsgq0 |
| `eq:cutoff_scales` | 3_5:830 | equation/figure label | ygdhmsgq0 |
| `eq:largea-b` | 3_5:840 | equation/figure label | ygdhmsgq0 |
| `eq;S123` | 3_5:844 | equation/figure label | ygdhmsgq0 |
| `eq:pointwise_loop2` | 3_5:848 | equation/figure label | ygdhmsgq0 |
| `eq_S1tilde` | 3_5:855 | equation/figure label | ygdhmsgq0 |
| `eq:boundwtS_1` | 3_5:860 | equation/figure label | ygdhmsgq0 |
| `eq_L2-J` | 3_5:872 | equation/figure label | ygdhmsgq0 |
| `eq:boundwtS31` | 3_5:878 | equation/figure label | ygdhmsgq0 |
| `Sec:Steps34` | 3_5:900 | section label | [sec 3_5:900 Steps 3 and 4: Sharp maximum estim] |
| `eq:CS1` | 3_5:936 | equation/figure label | ygdhmsgq |
| `eq;genWard0` | 3_5:950 | equation/figure label | ygdhmsgq |
| `eq;genWard1` | 3_5:955 | equation/figure label | ygdhmsgq |
| `defC=GEG` | 3_5:970 | equation/figure label | ygdhmsgq |
| `eq:Apsipsi` | 3_5:980 | equation/figure label | ygdhmsgq |
| `eq:Apsipsi1` | 3_5:985 | equation/figure label | ygdhmsgq |
| `eq:sumtwoloop` | 3_5:1069 | equation/figure label | lem:SEforLn |
| `eq:sumtwoloop2` | 3_5:1076 | equation/figure label | lem:SEforLn |
| `eq:Bu0asymp` | 3_5:1110 | equation/figure label | [Step3-proof: 3_5:1107] |
| `sahwNQ` | 3_5:1160 | equation/figure label | lem:STOeq_NQ |
| `NALsig_diff` | 3_5:1199 | equation/figure label | lem:STOeq_NQ |
| `eq:Ward_typeP` | 3_5:1264 | equation/figure label | Def:QtPt |
| `jywiiwsoks` | 3_5:1271 | equation/figure label | Def:QtPt |
| `zjuii1` | 3_5:1315 | equation/figure label | lem_+Q |
| `zjuii2` | 3_5:1318 | equation/figure label | lem_+Q |
| `int_K-L+Q` | 3_5:1337 | equation/figure label | lem_+Q |
| `eq:Xiiter` | 3_5:1381 | equation/figure label | lem:STOeq_Qt |
| `rela_XILXILK` | 3_5:1387 | equation/figure label | lem:STOeq_Qt |
| `sef8w483r324` | 3_5:1391 | equation/figure label | lem:STOeq_Qt |
| `adsyzz0s8d6` | 3_5:1396 | equation/figure label | lem:STOeq_Qt |
| `eq:iterative_pf_largeeta` | 3_5:1428 | equation/figure label | Eq:LGxb |
| `sec:1-s<L-2` | 3_5:1435 | section label | [Step3-proof: 3_5:1435] |
| `normQA2` | 3_5:1466 | equation/figure label | def;zero_mode_remove |
| `eq_L-Keee_nonzeromode` | 3_5:1540 | equation/figure label | lem: newPQ |
| `iisuwjyys` | 3_5:1545 | equation/figure label | lem: newPQ |
| `eq:psipara_smalletacase` | 3_5:1577 | equation/figure label | Eq:LGxb |
| `eq:iteration_improve_smalleta` | 3_5:1592 | equation/figure label | Eq:LGxb |
| `saww02` | 3_5:1606 | equation/figure label | [Step4-proof: 3_5:1602] |
| `ks-statements` | 3_5:1615 | section label | [sub 3_5:1615 Evolution kernel estimates] |
| `subsec:support` | 3_5:1674 | section label | [sub 3_5:1674 Proofs of supporting lemmas] |
| `eq:alternatecase1` | 3_5:1687 | equation/figure label | lem:STOeq_Qt |
| `y27kasdfg` | 3_5:1692 | equation/figure label | lem:STOeq_Qt |
| `A5` | 3_5:1698 | equation/figure label | lem:STOeq_Qt |
| `A4` | 3_5:1702 | equation/figure label | lem:STOeq_Qt |
| `eq:alternatecase2` | 3_5:1713 | equation/figure label | lem:STOeq_Qt |
| `am;asoi333` | 3_5:1775 | equation/figure label | lem:iterations |
| `xiu2n+2psi` | 3_5:1785 | equation/figure label | lem:iterations |
| `sadui_w0` | 3_5:1792 | equation/figure label | lem:iterations |
| `suauwiioo1` | 3_5:1832 | equation/figure label | lem:iterations |
| `eq:boundtwochains` | 3_5:1842 | equation/figure label | lem:iterations |
| `auskoppw2.00` | 3_5:1853 | equation/figure label | lem:iterations |
| `auskoppw2` | 3_5:1857 | equation/figure label | lem:iterations |
| `y2ussz` | 3_5:1871 | equation/figure label | lem: newPQ |
| `eq:y2ussz` | 3_5:1881 | equation/figure label | lem: newPQ |
| `eq:expandQAempty` | 3_5:1893 | equation/figure label | lem:STOeq_Qt_nonzero |
| `eq:kalpha1` | 3_5:1896 | equation/figure label | lem:STOeq_Qt_nonzero |
| `sahwNQ_smalleta` | 3_5:1903 | equation/figure label | lem:STOeq_Qt_nonzero |
| `sahwNQ2` | 3_5:1909 | equation/figure label | lem:STOeq_Qt_nonzero |
| `am;asoiuw_smalleta` | 3_5:1914 | equation/figure label | lem:STOeq_Qt_nonzero |
| `Sec:Step5` | 3_5:1935 | section label | [sec 3_5:1935 Step 5: Pointwise estimate for (cL] |
| `int_K-LcalE_n=2` | 3_5:1942 | equation/figure label | [sec 3_5:1935 Step 5: Pointwise estimate for (cL] |
| `eq:assmtlarge` | 3_5:1954 | equation/figure label | [sec 3_5:1935 Step 5: Pointwise estimate for (cL] |
| `eq:Step2_inputs` | 3_5:1961 | equation/figure label | [sub 3_5:1957 The case g2/L2le 1- tle 1-s le g2] |
| `S5WG+M000` | 3_5:1970 | equation/figure label | [sub 3_5:1957 The case g2/L2le 1- tle 1-s le g2] |
| `S5WG+M` | 3_5:1975 | equation/figure label | [sub 3_5:1957 The case g2/L2le 1- tle 1-s le g2] |
| `eq:decompU` | 3_5:1983 | equation/figure label | [sub 3_5:1957 The case g2/L2le 1- tle 1-s le g2] |
| `jymwons-L-K` | 3_5:1994 | equation/figure label | [sub 3_5:1957 The case g2/L2le 1- tle 1-s le g2] |
| `jymwons-Gc` | 3_5:1997 | equation/figure label | [sub 3_5:1957 The case g2/L2le 1- tle 1-s le g2] |
| `eq:def_calA5` | 3_5:2003 | equation/figure label | [sub 3_5:1957 The case g2/L2le 1- tle 1-s le g2] |
| `jymwons` | 3_5:2038 | equation/figure label | [sub 3_5:1957 The case g2/L2le 1- tle 1-s le g2] |
| `uuwmskiow` | 3_5:2046 | equation/figure label | [sub 3_5:1957 The case g2/L2le 1- tle 1-s le g2] |
| `iois-mtx` | 3_5:2053 | equation/figure label | [sub 3_5:1957 The case g2/L2le 1- tle 1-s le g2] |
| `uwp2-92kj` | 3_5:2058 | equation/figure label | [sub 3_5:1957 The case g2/L2le 1- tle 1-s le g2] |
| `uwftgwesj` | 3_5:2063 | equation/figure label | [sub 3_5:1957 The case g2/L2le 1- tle 1-s le g2] |
| `iois-mtx2` | 3_5:2067 | equation/figure label | [sub 3_5:1957 The case g2/L2le 1- tle 1-s le g2] |
| `iksjuwjx0` | 3_5:2072 | equation/figure label | [sub 3_5:1957 The case g2/L2le 1- tle 1-s le g2] |
| `uwkxkisjwj0` | 3_5:2084 | equation/figure label | [sub 3_5:1957 The case g2/L2le 1- tle 1-s le g2] |
| `uwkxkisjwj` | 3_5:2087 | equation/figure label | [sub 3_5:1957 The case g2/L2le 1- tle 1-s le g2] |
| `ilowkidjsw` | 3_5:2093 | equation/figure label | [sub 3_5:1957 The case g2/L2le 1- tle 1-s le g2] |
| `iksjuwjx` | 3_5:2105 | equation/figure label | [sub 3_5:1957 The case g2/L2le 1- tle 1-s le g2] |
| `eq:ells_to_ellt` | 3_5:2119 | equation/figure label | [sub 3_5:1957 The case g2/L2le 1- tle 1-s le g2] |
| `eq:ells_to_ellt2` | 3_5:2124 | equation/figure label | [sub 3_5:1957 The case g2/L2le 1- tle 1-s le g2] |
| `iksjuwjx2` | 3_5:2129 | equation/figure label | [sub 3_5:1957 The case g2/L2le 1- tle 1-s le g2] |
| `eq:PcalBterm` | 3_5:2137 | equation/figure label | [sub 3_5:1957 The case g2/L2le 1- tle 1-s le g2] |
| `eq:boundga` | 3_5:2142 | equation/figure label | [sub 3_5:1957 The case g2/L2le 1- tle 1-s le g2] |
| `iksjuwjx3` | 3_5:2150 | equation/figure label | [sub 3_5:1957 The case g2/L2le 1- tle 1-s le g2] |
| `eq:propcalB` | 3_5:2154 | equation/figure label | [sub 3_5:1957 The case g2/L2le 1- tle 1-s le g2] |
| `eq:boundEfar` | 3_5:2209 | equation/figure label | lem;CLT |
| `eq:main_challenge3` | 3_5:2214 | equation/figure label | lem;CLT |
| `eq:2p_product` | 3_5:2218 | equation/figure label | lem;CLT |
| `eq:sumregionsforb` | 3_5:2220 | equation/figure label | lem;CLT |
| `eq:pairingcond` | 3_5:2223 | equation/figure label | lem;CLT |
| `eq:2p_product_pair` | 3_5:2227 | equation/figure label | lem;CLT |
| `eq:simplecalculus` | 3_5:2234 | equation/figure label | lem;CLT |
| `eq:bound_isolated` | 3_5:2245 | equation/figure label | lem;CLT |
| `zYU1` | 3_5:2258 | equation/figure label | [sub 3_5:2251 The case g2/Ld leq 1-t leq 1-s leq] |
| `ThetaBcirc_infint` | 3_5:2264 | equation/figure label | [sub 3_5:2251 The case g2/Ld leq 1-t leq 1-s leq] |
| `uwp2-92kj00` | 3_5:2265 | equation/figure label | [sub 3_5:2251 The case g2/Ld leq 1-t leq 1-s leq] |
| `zYU2` | 3_5:2269 | equation/figure label | [sub 3_5:2251 The case g2/Ld leq 1-t leq 1-s leq] |
| `sec:Step5_larget` | 3_5:2284 | section label | [sub 3_5:2284 The case 1-t ge g2] |
| `def_WTuD` | 3_5:2297 | equation/figure label | [sub 3_5:2284 The case 1-t ge g2] |
| `eq:def_new_J*` | 3_5:2310 | equation/figure label | [sub 3_5:2284 The case 1-t ge g2] |
| `eq:def_TTT` | 3_5:2370 | equation/figure label | TailtoTail |
| `Sec:Step6` | 6:1 | section label | [sec 6:1 Step 6: Expected 2-loop estimates] |
| `Eexpint_K-L` | 6:4 | equation/figure label | [sec 6:1 Step 6: Expected 2-loop estimates] |
| `eq:Exp(L-K)1` | 6:61 | equation/figure label | lem:improve_exp_aver |
| `eq:Exp(L-K)2` | 6:65 | equation/figure label | lem:improve_exp_aver |
| `eq:LW-n=2` | 6:68 | equation/figure label | lem:improve_exp_aver |
| `eq:ExpLWn=2_smalleta` | 6:77 | equation/figure label | lem:improve_exp_aver |
| `eq:ExpL-Keasy` | 6:95 | equation/figure label | [Step6-proof: proof@6:93] |
| `eq:EPL-K` | 6:105 | equation/figure label | [Step6-proof: proof@6:93] |
| `int_K-L+QE` | 6:109 | equation/figure label | [Step6-proof: proof@6:93] |
| `eq:boundELKQ1` | 6:121 | equation/figure label | [Step6-proof: proof@6:93] |
| `eq:boundcommutator` | 6:128 | equation/figure label | [Step6-proof: proof@6:93] |
| `iisuwjyys_exp` | 6:142 | equation/figure label | [Step6-proof: proof@6:93] |
| `Sec:graph` | 7_8:1 | section label | [sec 7_8:1 Estimation of the light-weight ter] |
| `eq:EGC` | 7_8:10 | equation/figure label | [sec 7_8:1 Estimation of the light-weight ter] |
| `eq:directG1` | 7_8:17 | equation/figure label | [sec 7_8:1 Estimation of the light-weight ter] |
| `eq:directG2` | 7_8:25 | equation/figure label | [sec 7_8:1 Estimation of the light-weight ter] |
| `fxyG_sum` | 7_8:31 | equation/figure label | [sec 7_8:1 Estimation of the light-weight ter] |
| `eq:recolterm` | 7_8:41 | equation/figure label | [sec 7_8:1 Estimation of the light-weight ter] |
| `eq:recolterm2` | 7_8:45 | equation/figure label | [sec 7_8:1 Estimation of the light-weight ter] |
| `eq:recoltermwt` | 7_8:51 | equation/figure label | [sec 7_8:1 Estimation of the light-weight ter] |
| `eq:recoltermwt2` | 7_8:55 | equation/figure label | [sec 7_8:1 Estimation of the light-weight ter] |
| `eq:boundfxyGinf` | 7_8:62 | equation/figure label | [sec 7_8:1 Estimation of the light-weight ter] |
| `eq:far_ab` | 7_8:96 | equation/figure label | lem:LW_moment_exp |
| `sec:graphs` | 7_8:105 | section label | [sub 7_8:105 Graphical tools and local expansio] |
| `eq:def-Spm` | 7_8:110 | equation/figure label | [sub 7_8:105 Graphical tools and local expansio] |
| `scalemole` | 7_8:191 | equation/figure label | def_poly |
| `eq:estSpm-W` | 7_8:260 | equation/figure label | def scaling |
| `sec:graphs_ideas` | 7_8:402 | section label | [sub 7_8:402 Examples and nested property] |
| `yixi` | 7_8:876 | equation/figure label | def: BM2 |
| `eq:Gbyxi` | 7_8:880 | equation/figure label | def: BM2 |
| `eq:xia1a2` | 7_8:882 | equation/figure label | def: BM2 |
| `sec:pf_Anp` | 7_8:953 | section label | lem:Anp |
| `kwuyayw` | 7_8:1121 | equation/figure label | lem:Anp_key_gh |
| `eq:noA2` | 7_8:1146 | equation/figure label | lem:Anp_key_gh |
| `eq:induc_Ggraph` | 7_8:1166 | equation/figure label | lem:Anp_key_gh |
| `eq:change_of_order` | 7_8:1169 | equation/figure label | lem:Anp_key_gh |
| `eq:change_of_order2` | 7_8:1172 | equation/figure label | lem:Anp_key_gh |
| `kwuyayw_case1` | 7_8:1174 | equation/figure label | lem:Anp_key_gh |
| `eq:jthpath` | 7_8:1211 | equation/figure label | lem:Anp_key_gh |
| `eq:bound_new_graph` | 7_8:1233 | equation/figure label | lem:Anp_key_gh |
| `Fig:construct2B2` | 7_8:1331 | equation/figure label | lem:Anp_key_gh |
| `kwuyayw_case3` | 7_8:1344 | equation/figure label | lem:Anp_key_gh |
| `kwuyayw_ng` | 7_8:1397 | equation/figure label | lem:Anp_key_gh |
| `eq:degali` | 7_8:1404 | equation/figure label | lem:Anp_key_gh |
| `kwuyayw_ng_tree` | 7_8:1414 | equation/figure label | lem:Anp_key_gh |
| `Fig:construct_trees` | 7_8:1529 | equation/figure label | lem:Anp_key_gh |
| `subsec_pf_LW_moment_exp` | 7_8:1600 | section label | lem:LW_moment_exp |
| `eq:far_ab_K` | 7_8:1603 | equation/figure label | lem:LW_moment_exp |
| `adsuu33` | 7_8:1634 | equation/figure label | lem:LW_moment_exp_far |
| `adsuu44` | 7_8:1639 | equation/figure label | lem:LW_moment_exp_far |
| `adsuu_exp` | 7_8:1649 | equation/figure label | lem:LW_moment_exp_near |
| `adsuu_exp2` | 7_8:1655 | equation/figure label | lem:LW_moment_exp_near |
| `Fig:construct_keepT` | 7_8:1765 | equation/figure label | lem:LW_moment_exp_near |
| `sec:ext-to-BA` | 7_8:1792 | section label | [sec 7_8:1792 Extension to the block Anderson mo] |
| `eq:MG_conclusion3_BA` | 7_8:1999 | equation/figure label | lem_ConArg_BA |
| `eq:L-K2max_BA` | 7_8:2004 | equation/figure label | lem_ConArg_BA |
| `eq:Gronwall_dervJuD_BA` | 7_8:2009 | equation/figure label | lem_ConArg_BA |
| `eq:def2_stopping_BA` | 7_8:2013 | equation/figure label | lem_ConArg_BA |
| `eq:boundmgterm_BA` | 7_8:2017 | equation/figure label | lem_ConArg_BA |
| `eq:Gronwall_dervJuD_BA2` | 7_8:2022 | equation/figure label | lem_ConArg_BA |
| `eq:Gronwall_dervJuD_BA3` | 7_8:2026 | equation/figure label | lem_ConArg_BA |
| `eq_resolventunderpoly` | 7_8:2038 | equation/figure label | lem: EMn2_N |
| `eq:Psirelations` | 7_8:2046 | equation/figure label | lem: EMn2_N |
| `eq_resolventunderexp` | 7_8:2052 | equation/figure label | lem: EMn2_N |
| `eq_S1_bound_BA` | 7_8:2061 | equation/figure label | lem: EMn2_N |
| `eq:G+G-M` | 7_8:2067 | equation/figure label | lem: EMn2_N |
| `eq_resolventunderexp2` | 7_8:2091 | equation/figure label | lem: EMn2_N |
| `sec:pf_propTH` | A:9 | section label | lem_propTH |
| `eq;Taylor` | A:16 | equation/figure label | lem_propTH |
| `eq:shiftTaylor` | A:24 | equation/figure label | lem_propTH |
| `eq:expMLn` | A:28 | equation/figure label | lem_propTH |
| `eq:off_diagM` | A:32 | equation/figure label | lem_propTH |
| `eq:expMLn2` | A:39 | equation/figure label | lem_propTH |
| `ks` | A:84 | section label | [sub A:84 Proofs of evolution kernel estimat] |
| `eq:decompUalt` | A:100 | equation/figure label | lem:sum_Ndecay |
| `Xi_infint` | A:102 | equation/figure label | lem:sum_Ndecay |
| `eq:decomp_U2` | A:111 | equation/figure label | lem:sum_decay |
| `eq:decayXi` | A:115 | equation/figure label | lem:sum_decay |
| `sum_res_1_red0` | A:122 | equation/figure label | lem:sum_decay |
| `sum_res_1_red` | A:126 | equation/figure label | lem:sum_decay |
| `eq:1-sells2` | A:138 | equation/figure label | lem:sum_decay |
| `sum_res_deriv_red` | A:149 | equation/figure label | lem:sum_decay |
| `sum_res_2_red` | A:160 | equation/figure label | lem:sum_decay |
| `sum_res_deriv_red2` | A:168 | equation/figure label | lem:sum_decay |
| `eq:decompXii` | A:173 | equation/figure label | lem:sum_decay |
| `eq:Xibb` | A:179 | equation/figure label | lem:sum_decay |
| `eq:bddfA` | A:191 | equation/figure label | lem:sum_decay |
| `eq:latticesum_d3` | A:194 | equation/figure label | lem:sum_decay |
| `eq:samecolor` | A:209 | equation/figure label | lem:sum_decay_nonzero |
| `eq:diffcolor` | A:216 | equation/figure label | lem:sum_decay_nonzero |
| `sec:pfpropT` | A:230 | section label | lem:propT |
| `eq:smalletacase` | A:240 | equation/figure label | lem:propT |
| `eq:largeetacase` | A:247 | equation/figure label | lem:propT |
| `pf:claim_TTk` | A:265 | section label | claim:TTk |
| `eq:key_T_reudce_pf` | A:269 | equation/figure label | claim:TTk |
| `eq:TtTt` | A:278 | equation/figure label | claim:TTk |
| `eq:KtKt` | A:282 | equation/figure label | claim:TTk |
| `Sec:CalK` | A:315 | section label | [sub A:315 Basic properties of cal K-loops] |
| `example` | A:548 | equation/figure label | m-loop-tsp |
| `eq:defKpi` | A:611 | equation/figure label | tree-representation_BA |
| `eq_K-Kpi` | A:621 | equation/figure label | tree-representation_BA |
| `eq:molecule-Kpi` | A:625 | equation/figure label | tree-representation_BA |
| `eq:K-pi-bound` | A:675 | equation/figure label | ML:Kbound |
| `eq:wtKpi` | A:679 | equation/figure label | ML:Kbound |
| `eq:molecule-decay` | A:691 | equation/figure label | ML:Kbound |
| `eq:ind-step-bound` | A:703 | equation/figure label | ML:Kbound |
| `eq:shortexternal` | A:718 | equation/figure label | ML:Kbound |
| `eq:pointwise_Theta` | A:722 | equation/figure label | ML:Kbound |
| `eq:Sigma-empty-sum-zero` | A:731 | equation/figure label | ML:Kbound |
| `eq:f12` | A:749 | equation/figure label | ML:Kbound |
| `eq:Kpipi` | A:799 | equation/figure label | ML:Kbound |
| `eq:K-pi-bound_partial` | A:813 | equation/figure label | lem_wardineq_K |
| `subsec:pf-LWterm_EXP` | B:7 | section label | lem:LWterm_EXP |
| `eq:ELW_term` | B:13 | equation/figure label | lem:LWterm_EXP |
| `eq:termI1` | B:40 | equation/figure label | lem:LWterm_EXP |
| `eq:termI2` | B:47 | equation/figure label | lem:LWterm_EXP |
| `eq:termI41` | B:64 | equation/figure label | lem:LWterm_EXP |
| `eq;I42inG` | B:68 | equation/figure label | lem:LWterm_EXP |
| `eq;EGxy:x=y` | B:72 | equation/figure label | lem:LWterm_EXP |
| `Gammamuxy` | B:88 | equation/figure label | lem:LWterm_EXP |
| `eq:sizeGammamu_E` | B:92 | equation/figure label | lem:LWterm_EXP |
| `eq:GGraisesord` | B:99 | equation/figure label | lem:LWterm_EXP |
| `sec:pflocalregular` | B:122 | section label | lem:localregular |
| `eq:originGamma` | B:174 | equation/figure label | lem:localregular |
| `eq:initial_scaling` | B:201 | equation/figure label | lem:localregular |
| `eq:relateG1G0` | B:215 | equation/figure label | lem:localregular |
| `eq:ordGinter` | B:272 | equation/figure label | lem:localregular |
| `subsec:LWchange-to-BA` | B:286 | section label | lem:LWterm |
| `scaleatom` | B:317 | equation/figure label | def_atom |
| `Gyiyjatom` | B:424 | equation/figure label | lem:LW_moment |
| `eq:Gbyxi2_BA` | B:428 | equation/figure label | lem:LW_moment |
| `Gyiyjatom2` | B:432 | equation/figure label | lem:LW_moment |
| `eq:ordGaux_BAM` | B:486 | equation/figure label | lem:LW_moment |
| `G_by_auxG_BA` | B:489 | equation/figure label | lem:LW_moment |

Completeness (script): distinct active labels in the six TeX files = 617; labels in Part A rows = 333; labels in Part B = 284; sum = 617.

## Part C: labels that occur only in commented-out TeX lines (not part of the paper text; listed so that a raw `grep -n "\label{"` scan has no unexplained label)

| label | first TeX file:line | status |
|---|---|---|
| `just` | 1_2:55 | commented out (`%`) |
| `subsec_setting` | 1_2:260 | commented out (`%`) |
| `eq:submatrixnotation` | 1_2:280 | commented out (`%`) |
| `Japanesebracket` | 1_2:284 | commented out (`%`) |
| `Japanesebracket2` | 1_2:285 | commented out (`%`) |
| `eq:BA` | 1_2:365 | commented out (`%`) |
| `tau` | 1_2:422 | commented out (`%`) |
| `def_ellz` | 1_2:483 | commented out (`%`) |
| `MR:QDiff_EE` | 1_2:502 | commented out (`%`) |
| `eq:averm` | 1_2:637 | commented out (`%`) |
| `eq:SDE_Gt` | 1_2:730 | commented out (`%`) |
| `eq:mt_stay` | 1_2:761 | commented out (`%`) |
| `Def:stoch_flow` | 1_2:766 | commented out (`%`) |
| `GtEGz` | 1_2:796 | commented out (`%`) |
| `def:Ia` | 1_2:821 | commented out (`%`) |
| `taahCal` | 1_2:907 | commented out (`%`) |
| `eq:cut1` | 1_2:918 | commented out (`%`) |
| `lem-Ward` | 1_2:1016 | commented out (`%`) |
| `eq:Theta_WO` | 1_2:1080 | commented out (`%`) |
| `deri_Thxi` | 1_2:1094 | commented out (`%`) |
| `symmetry` | 1_2:1134 | commented out (`%`) |
| `ini)bigasya` | 1_2:1250 | commented out (`%`) |
| `Eq:Gdecay_w2a` | 1_2:1333 | commented out (`%`) |
| `usuayzoo` | 3_5:48 | commented out (`%`) |
| `sec:Inh_LE` | 3_5:59 | commented out (`%`) |
| `eq_L-K-1` | 3_5:77 | commented out (`%`) |
| `int_K-LcalE_simple` | 3_5:141 | commented out (`%`) |
| `TTT` | 3_5:331 | commented out (`%`) |
| `ll'` | 3_5:352 | commented out (`%`) |
| `lem:LWterm_exp` | 3_5:406 | commented out (`%`) |
| `eq:defJuD` | 3_5:585 | commented out (`%`) |
| `kwr3juw_type2` | 3_5:601 | commented out (`%`) |
| `sec:pf_STOeq_NQ` | 3_5:1152 | commented out (`%`) |
| `eq:boundPA` | 3_5:1294 | commented out (`%`) |
| `eq:sumzero666` | 3_5:1326 | commented out (`%`) |
| `pqthlk` | 3_5:1332 | commented out (`%`) |
| `eq:iteration_improve` | 3_5:1415 | commented out (`%`) |
| `def:A0sigma` | 3_5:1459 | commented out (`%`) |
| `am;asoi222_smalletacase` | 3_5:1564 | commented out (`%`) |
| `eq:iteration_induc_smalleta` | 3_5:1587 | commented out (`%`) |
| `sec:pf_STOeq_Qt_weak` | 3_5:1678 | commented out (`%`) |
| `lem: B45est` | 3_5:1691 | commented out (`%`) |
| `jfasiuu` | 3_5:1718 | commented out (`%`) |
| `eq:thetadot_bound` | 3_5:1733 | commented out (`%`) |
| `kkuuwsaf` | 3_5:1740 | commented out (`%`) |
| `kkuuwsaf5` | 3_5:1744 | commented out (`%`) |
| `sec:pf_iterations` | 3_5:1768 | commented out (`%`) |
| `Sec:pf_newPQ` | 3_5:1868 | commented out (`%`) |
| `sec:STOeq_Qt_nonzero` | 3_5:1890 | commented out (`%`) |
| `ThetaB_infint` | 3_5:2051 | commented out (`%`) |
| `ilow0pkkxmwsw` | 3_5:2100 | commented out (`%`) |
| `def_WTu` | 3_5:2292 | commented out (`%`) |
| `def_Ju` | 3_5:2301 | commented out (`%`) |
| `shoellJJ` | 3_5:2305 | commented out (`%`) |
| `lemma:step6-1` | 6:25 | commented out (`%`) |
| `jdasfuao01` | 6:51 | commented out (`%`) |
| `fxyG_sum2` | 7_8:35 | commented out (`%`) |
| `def_sub` | 7_8:154 | commented out (`%`) |
| `sec:local_exp` | 7_8:288 | commented out (`%`) |
| `eq;LWG2` | 7_8:405 | commented out (`%`) |
| `eq;L(3)` | 7_8:409 | commented out (`%`) |
| `eq:thelongedge` | 7_8:432 | commented out (`%`) |
| `eq_nested` | 7_8:1005 | commented out (`%`) |
| `def_auxgraph_gen` | 7_8:1027 | commented out (`%`) |
| `lem:Anp_2` | 7_8:1091 | commented out (`%`) |
| `GtEGz_BA` | 7_8:1804 | commented out (`%`) |
| `eq:Msym` | 7_8:1853 | commented out (`%`) |
| `symmetryM` | 7_8:1861 | commented out (`%`) |
| `symmetryP` | 7_8:1865 | commented out (`%`) |
| `eq:propm` | 7_8:1872 | commented out (`%`) |
| `eq:WardM1` | 7_8:1884 | commented out (`%`) |
| `eq:M-msc` | 7_8:1890 | commented out (`%`) |
| `def_asGMc2` | 7_8:1920 | commented out (`%`) |
| `GavLGEX_BA` | 7_8:1936 | commented out (`%`) |
| `55` | 7_8:1961 | commented out (`%`) |
| `eq:cont_T` | 7_8:1971 | commented out (`%`) |
| `defCALJ_deter` | 7_8:1995 | commented out (`%`) |
| `eq:reduce4to3_BA` | 7_8:2076 | commented out (`%`) |
| `eq:reduce4_bdd3_BA` | 7_8:2083 | commented out (`%`) |
| `m-graph-region` | A:433 | commented out (`%`) |
| `Fig:Mloop2` | A:464 | commented out (`%`) |
| `f-internalM` | A:576 | commented out (`%`) |
| `ML:Kbound+pi` | A:665 | commented out (`%`) |
| `eq:bcal_k_2` | A:667 | commented out (`%`) |
| `eq:twodiagonal_edge` | B:224 | commented out (`%`) |
| `eq:twodiagonal_weight` | B:240 | commented out (`%`) |
| `simplemolecule` | B:450 | commented out (`%`) |

Raw scan (script): 704 distinct `\label{...}` strings in the six files = 617 active (Parts A and B) + 87 only in comments (Part C).

## Checks (script output)

Generated: Fri Oct  2 18:51:26 UTC 2026 (`date -u`).  Declaration indexes: RBM3D `main` 619 declarations (`decls.py RBM3D`, worktree `t/T2001` before the probe), RBM2D `c9a24cf` 13394 declarations (`decls.py RBM2D`).

`python3 verify.py` (every Lean citation of Part A, RBM3D by file:line grep in the worktree, RBM2D by `git -C ../RBM2D --no-optional-locks grep -n -E "(theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque) " c9a24cf -- <file>`):

```
RBM3D citations: 138 distinct declarations, 138 verified at the cited file:line, 0 mismatches
RBM2D citations: 128 distinct declarations in 72 files, 128 verified by git grep -n at c9a24cf, 0 mismatches
```


`python3 propscan.py` (merged theorems/defs of RBM3D `main` whose signature mentions an unproved Prop; used for the old-mode classification in the prove report):

```
ThetaDecayShort  7 Loop.pureLoop_two_kTwoLoop Loop.norm_Theta_same_le_exp Loop.pureLoop_two Loop.pureLoop_three Loop.pureLoop_two_of_isKLoop exists_norm_uKer_same_le norm_zeroModeSet_UN_le
ThetaDecay       3 norm_XiKer_apply_le sum_ball_norm_XiKer_le sum_prod_norm_XiKer_le
ThetaDiffOne     0 
ThetaDiffTwo     0 
ThetaZeroMode    2 exists_norm_projMat_mul_uKer_le norm_zeroModeSet_UN_le
PropTH           0 
KTreeRep         0 
KLoopBound       0 
TwoLoopBounded   4 Loop.kThree_eq_of_isKLoop Loop.pureLoop_three Loop.kTwoFormula_of_isKLoop Loop.pureLoop_two_of_isKLoop
```

## Appendix: the scripts (run in one directory: `python3 decls.py RBM3D > decls3d.tsv`; the same on the RBM2D snapshot > `decls2d.tsv`; `python3 emit.py out.md`; `python3 verify.py`)

`mapping.py` is the hand-written input (gate, scope, class, Lean and RBM2D names per row); its content is the table above.

### `decls.py`

```python
#!/usr/bin/env python3
"""Extract declarations (file, line, kind, private, full name, signature) from a Lean tree.
usage: decls.py ROOT_DIR [SUBDIR_PREFIX ...]   -> TSV on stdout"""
import re, sys, os

DECL = re.compile(r'^(\s*)((?:@\[[^\]]*\]\s*)*)((?:(?:private|protected|noncomputable|unsafe|partial|nonrec)\s+)*)(theorem|lemma|def|structure|abbrev|class|inductive|instance|opaque|axiom)\b\s*(.*)$')
NS = re.compile(r'^namespace\s+(\S+)')
END = re.compile(r'^end(?:\s+(\S+))?\s*$')
SEC = re.compile(r'^section(?:\s+(\S+))?\s*$')

def sig_of(lines, i, first_rest):
    # accumulate text from line i until first top-level ':=' / 'where' / '|' (for inductive)
    text = lines[i]
    j = i
    out = []
    depth = 0
    buf = ''
    # build full text up to 40 lines
    chunk = []
    for k in range(i, min(i+60, len(lines))):
        chunk.append(lines[k])
    s = '\n'.join(chunk)
    # strip comments
    s2 = re.sub(r'--[^\n]*', '', s)
    res = []
    d = 0
    n = len(s2)
    p = 0
    while p < n:
        c = s2[p]
        if c in '([{⟨':
            d += 1
        elif c in ')]}⟩':
            d -= 1
        if d <= 0:
            if s2.startswith(':=', p):
                break
            if s2.startswith(' where', p) or s2.startswith('\nwhere', p):
                break
            if s2.startswith('\n  | ', p) or s2.startswith('\n| ', p):
                break
            if s2.startswith('\n  deriving', p):
                break
        res.append(c)
        p += 1
    return re.sub(r'\s+', ' ', ''.join(res)).strip()

def main(root, prefixes):
    for dp, dn, fn in os.walk(root):
        for f in sorted(fn):
            if not f.endswith('.lean'):
                continue
            path = os.path.join(dp, f)
            rel = os.path.relpath(path, os.getcwd())
            if prefixes and not any(rel.startswith(x) for x in prefixes):
                continue
            lines = open(path, encoding='utf8').read().split('\n')
            stack = []  # (kind, name)
            in_comment = False
            for i, line in enumerate(lines):
                st = line.strip()
                # crude block comment tracking
                if in_comment:
                    if '-/' in line:
                        in_comment = False
                    continue
                if st.startswith('/-') and '-/' not in st:
                    in_comment = True
                    continue
                if st.startswith('/-') and '-/' in st:
                    continue
                m = NS.match(line)
                if m:
                    stack.append(('ns', m.group(1)))
                    continue
                m = SEC.match(line)
                if m:
                    stack.append(('sec', m.group(1) or ''))
                    continue
                m = END.match(line)
                if m:
                    if stack:
                        stack.pop()
                    continue
                m = DECL.match(line)
                if m:
                    mods = m.group(3) or ''
                    kind = m.group(4)
                    rest = m.group(5)
                    nm = re.match(r'([^\s:({\[⟨]+)', rest)
                    name = nm.group(1) if nm else ''
                    nsname = '.'.join(x[1] for x in stack if x[0] == 'ns')
                    if name.startswith('_root_.'):
                        full = name[len('_root_.'):]
                    else:
                        full = (nsname + '.' + name) if nsname and name else (name or nsname)
                    sig = sig_of(lines, i, rest)
                    priv = 'private' if 'private' in mods else ''
                    print('\t'.join([rel, str(i+1), kind, priv, full, sig]))

if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2:])
```

### `graph2.py`

```python
#!/usr/bin/env python3
"""Result rows, section pseudo-nodes, owners of every TeX line, reference graph, reachability."""
import re, json, sys
root = '/Users/junyin/Lean_proof/RBM3D/paper/tex/'
FILES = ['1_2_Intro_model_result.tex','3_5_Loop_Hierarchy.tex','6_Step6_two_loop.tex',
         '7_8_light_weight.tex','A_deterministic_estimates.tex','B_graphical_lemmas.tex']
SHORT = {'1_2_Intro_model_result.tex':'1_2','3_5_Loop_Hierarchy.tex':'3_5','6_Step6_two_loop.tex':'6','7_8_light_weight.tex':'7_8','A_deterministic_estimates.tex':'A','B_graphical_lemmas.tex':'B'}
THM = ('theorem','lemma','proposition','definition','corollary','claim','assumption','remark','remarks','conjecture','notation','example','strategy','thmx')
KEYEQ = '''def:ilambda stoch_domination eq:blockIa representativeL bandcw0 eq:variancematrix def_Green
eq:defmzsc eq:defMzsc eq:spectral_domain eq:calBetaK eq:BetaK def:Theta ssfa2 ssfa2_deter
bandcwV eq:H_blocka eq:Psi3D self_m def_G0 MBM def_G0t eq:opS eq_Ward0 eq_Ward
lRB1 Gtmwc Gt_bound_flow Gt_avgbound_flow Eq:Gdecay_w Eq:LGxb Eq:L-KGt-flow Eq:Gdecay_flow
Eq:Gdecay+s<g_flow Eq:Gtlp_exp_flow eq_L-Keee DefKsimLK def_ELKLK defCALJ eq:def2_stopping
Gronwall_inequality def:XiL def:XIL-K eq:spectral_domainBA eq:ukx
eq:simpleboundK eq:opt_L2 eq:Gronwall_dervJuD awi2iks LK_simple'''.split()
def strip_comment(line):
    out=[];i=0
    while i<len(line):
        c=line[i]
        if c=='\\' and i+1<len(line):
            out.append(line[i:i+2]);i+=2;continue
        if c=='%':break
        out.append(c);i+=1
    return ''.join(out)
REFRE = re.compile(r'\\(?:Cref|cref|ref|eqref|autoref)\{([^}]*)\}')
def refs_in(text):
    out=[]
    for m in REFRE.finditer(text):
        out += [l.strip() for l in m.group(1).split(',')]
    return out
def balanced(line, k):
    depth=1; t=''
    while k<len(line) and depth>0:
        c=line[k]
        if c=='{': depth+=1
        elif c=='}':
            depth-=1
            if depth==0: break
        t+=c; k+=1
    return t
def clean_title(t):
    t=re.sub(r'\\texorpdfstring\{((?:[^{}]|\{[^{}]*\})*)\}\{[^}]*\}',r'\1',t)
    t=re.sub(r'\\(?:Cref|ref)\{([^}]*)\}',r'\1',t)
    t=t.replace('\\ilambda','g')
    t=re.sub(r'[\\${}^_]','',t)
    return re.sub(r'\s+',' ',t)

def build():
    data={f:[(i+1,strip_comment(l)) for i,l in enumerate(open(root+f,encoding='utf8').read().split('\n'))] for f in FILES}
    envs=[];labels=[];sections=[]
    for f in FILES:
        stack=[]
        for ln,line in data[f]:
            for m in re.finditer(r'\\(section|subsection|subsubsection|paragraph)\*?\{',line):
                t=balanced(line,m.end())
                lab=re.search(r'\\label\{([^}]*)\}',line)
                sections.append(dict(file=f,line=ln,kind=m.group(1),title=clean_title(t),raw=t,label=lab.group(1) if lab else None))
            for m in re.finditer(r'\\begin\{(\w+\*?)\}(\[([^\]]*)\])?',line):
                nm=m.group(1).rstrip('*')
                if nm in THM: stack.append(dict(file=f,start=ln,env=nm,title=m.group(3) or '',labels=[],end=None))
            for m in re.finditer(r'\\label\{([^}]*)\}',line):
                labels.append(dict(file=f,line=ln,label=m.group(1),inenv=(stack[-1]['labels'][0] if stack and stack[-1]['labels'] else (None))))
                if stack: stack[-1]['labels'].append(m.group(1))
            for m in re.finditer(r'\\end\{(\w+\*?)\}',line):
                nm=m.group(1).rstrip('*')
                if nm in THM and stack and stack[-1]['env']==nm:
                    e=stack.pop(); e['end']=ln; envs.append(e)
    envs.sort(key=lambda e:(FILES.index(e['file']),e['start']))
    rows=[];node_of_label={}
    for e in envs:
        if not e['labels']: continue
        rid=e['labels'][0]
        rows.append(dict(id=rid,file=e['file'],line=e['start'],kind=e['env'],title=clean_title(e['title']),labels=list(e['labels']),end=e['end'],node='row'))
        for l in e['labels']: node_of_label[l]=rid
    first_loc={}
    for L in labels: first_loc.setdefault(L['label'],(L['file'],L['line']))
    for k in KEYEQ:
        if k in node_of_label: continue
        f,ln=first_loc[k]
        rows.append(dict(id=k,file=f,line=ln,kind='eq/def',title='',labels=[k],end=ln,node='row'))
        node_of_label[k]=k
    rows.sort(key=lambda r:(FILES.index(r['file']),r['line']))
    # section pseudo nodes
    secnodes=[]
    for s in sections:
        t=s['title']
        st=re.search(r'Proof of Step (\d)',t)
        mref=re.search(r'Proof of.*?\\(?:Cref|ref)\{([^}]*)\}',s['raw'])
        if st: nid='[Step%s-proof: %s]'%(st.group(1),SHORT[s['file']]+':'+str(s['line']))
        elif mref: nid=None  # owner is the referenced row
        else: nid='[%s %s:%d %s]'%(s['kind'][:3],SHORT[s['file']],s['line'],t[:34])
        s['node']=nid
        if mref: s['owner_row']=[x.strip() for x in mref.group(1).split(',')]
        if s['label']:
            node_of_label[s['label']]=nid if nid else mref.group(1).split(',')[0].strip()
        if nid: secnodes.append(nid)
    # owners per line
    owner={}
    for f in FILES:
        marks=[]
        for r in rows:
            if r['file']==f and r['kind'] not in ('remark','remarks','example','strategy'): marks.append((r['line'],1,('row',r['id'])))
        for s in sections:
            if s['file']==f: marks.append((s['line'],0,('sec',s)))
        marks.sort(key=lambda x:(x[0],x[1]))
        cur=['[front %s]'%SHORT[f]]; mi=0; override=None
        for ln,text in data[f]:
            while mi<len(marks) and marks[mi][0]<=ln:
                kind,obj=marks[mi][2]
                if kind=='row': cur=[obj]
                else:
                    if obj.get('owner_row'): cur=obj['owner_row']
                    else: cur=[obj['node']]
                mi+=1
            # proof environments with titles
            m=re.search(r'\\begin\{proof\}\[([^\]]*)\]',text)
            if m:
                t=m.group(1)
                st=re.search(r'Step (\d)',t)
                refs=[x for x in refs_in(t)]
                if st: override=['[Step%s-proof: %s]'%(st.group(1),'proof@'+SHORT[f]+':'+str(ln))]
                elif 'Proof of' in t and refs:
                    override=[node_of_label.get(x,x) for x in refs if x in node_of_label] or None
                else: override=None
            owner[(f,ln)]=override if override else cur
            if re.search(r'\\end\{proof\}',text): override=None
    return data,rows,labels,sections,node_of_label,owner,envs,secnodes

def graph(data,rows,node_of_label,owner):
    uses={}   # owner node -> {row: [(f,ln)]}
    for f in FILES:
        for ln,text in data[f]:
            for l in refs_in(text):
                n=node_of_label.get(l)
                if n is None: continue
                for o in owner[(f,ln)]:
                    if o==n: continue
                    uses.setdefault(o,{}).setdefault(n,[]).append((f,ln))
    return uses

if __name__=='__main__':
    data,rows,labels,sections,nol,owner,envs,secnodes=build()
    uses=graph(data,rows,nol,owner)
    json.dump(dict(rows=rows,node_of_label=nol,secnodes=secnodes,
                   uses={o:{n:v for n,v in d.items()} for o,d in uses.items()}),open('graph2.json','w'),ensure_ascii=False)
    print(len(rows),'rows',len(secnodes),'section nodes',len(labels),'labels')
    # reachability from endpoints
    endpoints=['MR:decol','MR:locSC','MR:QUE','Thm: B_Univ','MR:QuDiff','MR:decol_BA']
    struct={}
    # lem:main_ind is proved by Steps 1-6 = sections 3-6 (paper 1_2:1313)
    struct['lem:main_ind']=[n for n in secnodes if re.search(r'\[(sec|sub|par|Step)',n) and not n.startswith('[sec 1_2') ] 
    # section nodes use the rows stated inside their line range
    allmarks=sorted([(sec['file'],sec['line'],sec) for sec in sections],key=lambda x:(FILES.index(x[0]),x[1]))
    for i,(f,ln,sec) in enumerate(allmarks):
        hi=10**9
        if i+1<len(allmarks) and allmarks[i+1][0]==f: hi=allmarks[i+1][1]
        owners=sec.get('owner_row') or [sec['node']]
        inside=[r['id'] for r in rows if r['file']==f and ln<=r['line']<hi]
        for o in owners:
            struct.setdefault(o,[]).extend(inside)
    reach=set(endpoints); todo=list(endpoints)
    while todo:
        o=todo.pop()
        outs=set(uses.get(o,{}).keys())|set(struct.get(o,[]))
        for n in outs:
            if n not in reach: reach.add(n); todo.append(n)
    rowids=[r['id'] for r in rows]
    print('rows reached:',sum(1 for r in rowids if r in reach),'of',len(rowids))
    print('NOT reached:',[r for r in rowids if r not in reach])
```

### `elab.py`

```python
#!/usr/bin/env python3
"""Elaborated types of the cited RBM3D definitions (`#check @name`, pp.width 4000), written to elab.json.
Needed because binders introduced by `variable` do not show in the source signature."""
import sys, json, re, subprocess
sys.path.insert(0, '.')
import mapping, render as RD
WT = '/Users/junyin/Lean_proof/RBM3D-wt/T2001'
names = []
for m in mapping.ROWS + mapping.PSEUDO:
    for n in m['lean']:
        fn = RD.full(n)
        r = RD.IDX3[fn]
        if r[2] in ('def', 'abbrev', 'structure', 'instance') and fn not in names:
            names.append(fn)
lines = ['import RBM3D', 'set_option pp.width 4000', 'set_option pp.unicode.fun true']
for n in names:
    lines.append('#check @%s' % n)
open('chk_defs.lean', 'w', encoding='utf8').write('\n'.join(lines) + '\n')
out = subprocess.run(['lake', 'env', 'lean', '/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/chk_defs.lean'],
                     cwd=WT, capture_output=True, text=True)
txt = out.stdout + out.stderr
res = {}
cur = None
for l in txt.split('\n'):
    m = re.match(r'^@?(RBM\.[^\s:]+) : (.*)$', l)
    if m:
        cur = m.group(1); res[cur] = m.group(2)
    elif cur and l.startswith(' '):
        res[cur] += ' ' + l.strip()
    elif l.strip():
        cur = None
        print('UNPARSED:', l[:160])
for n in names:
    if n not in res: print('MISSING', n)
json.dump({k: re.sub(r'\s+', ' ', v) for k, v in res.items()}, open('elab.json', 'w'), ensure_ascii=False, indent=0)
print(len(names), 'defs;', len(res), 'types')
```

### `render.py`

```python
#!/usr/bin/env python3
"""Render docs/reports/T2001-coverage.md from: the TeX scan (graph2.py), the Lean declaration indexes
(decls.py on RBM3D main and on the RBM2D snapshot of c9a24cf) and the hand mapping (mapping.py)."""
import re, sys, json, collections
sys.path.insert(0, '.')
import graph2, mapping

D3 = [l.rstrip('\n').split('\t') for l in open('decls3d.tsv')]
D2 = [l.rstrip('\n').split('\t') for l in open('decls2d.tsv')]
IDX3 = {}
for r in D3: IDX3.setdefault(r[4], r)
IDX2 = {}
for r in D2: IDX2.setdefault(r[4], r)

def full(n): return n if n.startswith('RBM.') else 'RBM.' + n

def esc(s): return s.replace('|', '\\|').replace('\n', ' ')

import json as _json, os as _os
ELAB = _json.load(open('elab.json')) if _os.path.exists('elab.json') else {}
def sig3(name, maxlen=520):
    r = IDX3[name]
    sig = r[5]
    # drop the leading modifiers/keyword+name duplication: keep the extracted text
    if len(sig) > maxlen: sig = sig[:maxlen] + ' …[cut at %d chars]' % maxlen
    out = '%s:%s `%s`' % (r[0].replace('RBM3D/', ''), r[1], esc(sig))
    if name in ELAB:
        t = ELAB[name]
        if len(t) > 300: t = t[:300] + ' …'
        out += ' ⟦#check: `%s`⟧' % esc(t)
    return out

def loc2(name):
    r = IDX2[name]
    return '%s:%s `%s`' % (r[0].replace('RBM2D/', ''), r[1], r[4].replace('RBM.', ''))

data, rows, labels, sections, nol, owner, envs, secnodes = graph2.build()
uses = graph2.graph(data, rows, nol, owner)
rowby = {r['id']: r for r in rows}
first_loc = {}
for L in labels: first_loc.setdefault(L['label'], (L['file'], L['line']))
SHORT = graph2.SHORT

# consumers: owners that reference any label of the row
def consumers_of(rid):
    r = rowby.get(rid)
    labs = set(r['labels']) if r else {rid}
    out = collections.OrderedDict()
    for o, d in uses.items():
        for n in d:
            if n in (rid,) :
                out.setdefault(o, 0); out[o] += len(d[n])
    # references to the row's sub-labels resolve to the row id via node_of_label, so the above suffices
    return out

# citation snippets in the region owned by the row
CITE = re.compile(r'\\cite[a-z]*(?:\[[^\]]*\])?\{([^}]*)\}')
CTX = re.compile(r'((?:Lemma|Theorem|Section|Appendix|Claim|equation|equations|Definition|Remark)\s+[\w.()\-]+(?:\s+of)?)\s*$')
INTERNAL5 = {'YY_25','DYYY25','RBSO1D','yang2024Del','yang2021delocalization','yang2021random','LeeSchSteYau2015',
             'Aizenman_book','Xu:2024aa','bourgade2019random','Lawler_book','Biane'}
def cites_of(rid):
    out = []
    for f in graph2.FILES:
        for ln, text in data[f]:
            if rid in owner[(f, ln)]:
                for m in CITE.finditer(text):
                    pre = text[max(0, m.start() - 70):m.start()]
                    cm = CTX.search(pre)
                    for k in m.group(1).split(','):
                        k = k.strip()
                        out.append((k, SHORT[f] + ':' + str(ln), cm.group(1) if cm else ''))
    return out

def fmt_cites(rid, extra):
    cs = cites_of(rid)
    keys = collections.OrderedDict(); others = collections.OrderedDict()
    for k, loc, ctx in cs:
        if k in INTERNAL5:
            if ('[%s]' % k) not in extra:
                keys.setdefault(k, (ctx, loc))
        else:
            others.setdefault(k, loc)
    parts = ['[%s]%s@%s' % (k, (' ' + ctx) if ctx else '', loc) for k, (ctx, loc) in keys.items()]
    s = '; '.join(parts[:4]) + (' …(+%d)' % (len(parts) - 4) if len(parts) > 4 else '')
    if extra:
        s = (s + '; ' if s else '') + extra
    if s: s = 'internal by DECISIONS §5: ' + s
    if others:
        o = ', '.join('[%s]@%s' % (k, loc) for k, loc in list(others.items())[:5]) + (' …(+%d)' % (len(others) - 5) if len(others) > 5 else '')
        s = (s + '; ' if s else '') + 'other cited keys in the row region (outside the DECISIONS §2 inventory): ' + o
    return s

def row_loc(base):
    r = rowby.get(base)
    if r: return r['file'], r['line'], r['kind'], r['title'], r['labels']
    if base in first_loc:
        f, ln = first_loc[base]
        return f, ln, 'sub-label/eq', '', [base]
    raise KeyError(base)

def render():
    out = []
    problems = []
    seen_bases = set()
    table = []
    for k, m in enumerate(mapping.ROWS):
        rid = m['id']; base = rid.split('#')[0]
        seen_bases.add(base)
        try:
            f, ln, kind, title, labs = row_loc(base)
        except KeyError:
            problems.append('no TeX row for ' + rid); continue
        lean_cells = []
        for n in m['lean']:
            fn = full(n)
            if fn not in IDX3: problems.append('RBM3D name missing: %s (row %s)' % (fn, rid)); continue
            lean_cells.append(sig3(fn))
        r2_cells = []
        for n in m['r2d']:
            fn = full(n)
            if fn not in IDX2: problems.append('RBM2D name missing: %s (row %s)' % (fn, rid)); continue
            r2_cells.append(loc2(fn))
        cons = consumers_of(base)
        cons_list = [c for c in cons.keys()]
        cons_s = ', '.join(cons_list[:6]) + (' …(+%d)' % (len(cons_list) - 6) if len(cons_list) > 6 else '')
        if not cons_s: cons_s = '(none cited; statement/definition)'
        src = fmt_cites(base, m['src'])
        table.append(dict(n=k + 1, id=rid, base=base, file=SHORT[f], line=ln, kind=kind + ((' [' + title[:28] + ']') if title else ''),
                          gate=m['gate'], scope=m['scope'], cls=m['cls'], lean=lean_cells, r2=r2_cells, r2note=m['r2dnote'],
                          note=m['note'], cons=cons_s, ncons=len(cons_list), src=src, labs=labs))
    return table, problems, seen_bases

if __name__ == '__main__':
    table, problems, seen = render()
    print('rows in mapping:', len(table), 'problems:', len(problems))
    for p in problems: print('  PROBLEM', p)
    missing = [r['id'] for r in rows if r['id'] not in seen]
    print('graph rows without mapping:', missing)
    print('classes:', collections.Counter(t['cls'] for t in table))
```

### `emit.py`

```python
#!/usr/bin/env python3
import sys, re, collections, subprocess, datetime
sys.path.insert(0,'.')
import render as RD, mapping, graph2
from render import full, esc, sig3, loc2, IDX3, IDX2, SHORT

def cell(items, sep='<br>'):
    return sep.join(items) if items else 'none'

def main(outpath):
    table, problems, seen = RD.render()
    assert not problems, problems
    # pseudo rows
    extra = []
    for k, m in enumerate(mapping.PSEUDO):
        lean_cells = []
        for n in m['lean']:
            fn = full(n); assert fn in IDX3, fn
            lean_cells.append(sig3(fn))
        r2_cells = []
        for n in m['r2d']:
            fn = full(n); assert fn in IDX2, fn
            r2_cells.append(loc2(fn))
        extra.append(dict(n=len(table)+k+1, id=m['id'], base=m['id'], file=m['file'], line=m['line'], kind=m['kind'], gate=m['gate'],
                          scope=m['scope'], cls=m['cls'], lean=lean_cells, r2=r2_cells, r2note='', note=m['note'],
                          cons='(none cited)', ncons=0, src=m['src'], labs=[]))
    table += extra
    allrows = table
    # labels covered by Part A
    covered = set()
    for r in graph2_rows():
        covered.update(r['labels'])
    partA_labels = covered
    L = []
    w = L.append
    w('# T2001 coverage table (dependency table of the survey)')
    w('')
    w('Produced by the scripts reproduced in the appendix (TeX scan, declaration index of RBM3D `main` and of RBM2D `c9a24cf`, hand mapping rendered by `render.py`).')
    w('Sources: paper TeX `paper/tex/*.tex` (comments stripped before scanning); RBM3D Lean at worktree `t/T2001` = `main` `3c11d7b` (`RBM3D/` before the probe); RBM2D snapshot `git -C ../RBM2D --no-optional-locks archive c9a24cf RBM2D`.')
    w('')
    w('**Class** (of the Lean statement against the paper statement, signatures only; docstrings are not evidence, CLAUDE.md 5.7, 5.10): '
      '`i` proved as stated, no extra hypotheses; `ii` proved only conditionally (unproved hypotheses / Prop parameters listed); '
      '`iii` special case only (restriction named); `iv` absent (no declaration on main states it; declarations listed in the Lean column are ingredients or Prop placeholders, said so in the note).  '
      'A row split into parts `#..` has one class per part.  **Scope**: `band` the Lean/paper statement is for the random band model only, `BA` block Anderson only, `both`.  '
      '**Gate**: the gate of `docs/ROUTES.md` that owns the row (`F0 MD PT KL EK ST LW MA UN BA`; `-` for remarks/examples).  '
      '**Consumers**: rows or section pseudo-nodes (`[sec file:line title]`, `[StepN-proof ..]`) whose statement or proof text cites a label of the row (script, nearest enclosing row or section; at most 6 shown).  '
      '**§5 source**: the row region cites one of the items of DECISIONS 5 (script: `\\cite` keys in the region of the row) or the hand note names it; such rows are internal by DECISIONS 5.')
    w('')
    # stats
    cc = collections.Counter(t['cls'] for t in allrows)
    gc = collections.defaultdict(collections.Counter)
    for t in allrows: gc[t['gate']][t['cls']] += 1
    w('## Summary (script)')
    w('')
    w('- rows: %d (TeX rows %d + pseudo rows %d); classes: i=%d, ii=%d, iii=%d, iv=%d' % (len(allrows), len(table)-len(extra), len(extra), cc['i'], cc['ii'], cc['iii'], cc['iv']))
    w('- per gate (i/ii/iii/iv): ' + '; '.join('%s %d/%d/%d/%d' % (g, gc[g]['i'], gc[g]['ii'], gc[g]['iii'], gc[g]['iv']) for g in sorted(gc)))
    routes = open('/Users/junyin/Lean_proof/RBM3D/docs/ROUTES.md', encoding='utf8').read()
    cand = [t for t in allrows if t['gate'] != '-' and not t['id'].startswith('[')]
    notnamed = [t for t in cand if t['id'].split('#')[0] not in routes]
    w('- rows with a gate (excluding %d remark/example rows and %d pseudo rows): %d; label literally named in `docs/ROUTES.md`: %d; not literally named: %d (by gate: %s)' % (
        sum(1 for t in allrows if t['gate'] == '-'), len(extra), len(cand), len(cand) - len(notnamed), len(notnamed),
        ', '.join('%s %d' % (g, n) for g, n in collections.Counter(t['gate'] for t in notnamed).most_common())))
    w('')
    w('## Part A: result rows (one row per line)')
    w('')
    w('| # | row (paper label) | labels in row | TeX file:line | kind | gate | scope | class | Lean on main: file:line `signature` (script-extracted) | restriction / unproved hypotheses / note | consumers (script) | RBM2D analogue at c9a24cf (file:line `declaration`) | §5 source |')
    w('|---|---|---|---|---|---|---|---|---|---|---|---|---|')
    for t in allrows:
        labs = t['labs']
        labs_s = ', '.join(labs[:8]) + (' …(+%d)' % (len(labs)-8) if len(labs) > 8 else '')
        r2 = cell(t['r2'])
        if t['r2note']: r2 = (r2 + ' — ' if t['r2'] else '') + t['r2note']
        elif not t['r2']: r2 = 'none'
        w('| %d | `%s` | %s | %s:%s | %s | %s | %s | %s | %s | %s | %s | %s | %s |' % (
            t['n'], esc(t['id']), esc(labs_s), t['file'], t['line'], esc(t['kind']), t['gate'], t['scope'], t['cls'],
            esc(cell(t['lean'])) if False else cell(t['lean']), esc(t['note']), esc(t['cons']), r2, esc(t['src']) if t['src'] else ''))
    w('')
    # Part B
    w('## Part B: every other `\\label` of the TeX (one label per line)')
    w('')
    w('Labels that are neither the label of a Part A row nor a sub-label listed in its `labels in row` cell: displayed equations inside proofs, section labels, figure labels.  `inside` is the nearest enclosing Part A row or section node (script).')
    w('')
    w('| label | TeX file:line | kind | inside |')
    w('|---|---|---|---|')
    secl = {s['label']: s for s in graph2sections() if s['label']}
    nB = 0
    seenB = set()
    for Lb in graph2labels():
        lab = Lb['label']
        if lab in partA_labels or lab in seenB: continue
        seenB.add(lab)
        f = Lb['file']; ln = Lb['line']
        kind = 'section label' if lab in secl else 'equation/figure label'
        ins = owner_of(f, ln)
        w('| `%s` | %s:%d | %s | %s |' % (esc(lab), SHORT[f], ln, kind, esc(ins)))
        nB += 1
    nTot = len({Lb['label'] for Lb in graph2labels()})
    w('')
    w('Completeness (script): distinct active labels in the six TeX files = %d; labels in Part A rows = %d; labels in Part B = %d; sum = %d.' % (nTot, len(partA_labels), nB, len(partA_labels)+nB))
    # Part C: labels that occur only in commented-out lines
    import re as _re
    raw = collections.OrderedDict()
    for f in graph2.FILES:
        for i, l in enumerate(open(graph2.root + f, encoding='utf8').read().split('\n')):
            for m in _re.finditer(r'\\label\{([^}]*)\}', l):
                raw.setdefault(m.group(1), (SHORT[f], i + 1))
    active_all = {Lb['label'] for Lb in graph2labels()}
    only_c = [(k, v) for k, v in raw.items() if k not in active_all]
    w('')
    w('## Part C: labels that occur only in commented-out TeX lines (not part of the paper text; listed so that a raw `grep -n "\\label{"` scan has no unexplained label)')
    w('')
    w('| label | first TeX file:line | status |')
    w('|---|---|---|')
    for k, (sf, ln) in only_c:
        w('| `%s` | %s:%d | commented out (`%%`) |' % (esc(k), sf, ln))
    w('')
    w('Raw scan (script): %d distinct `\\label{...}` strings in the six files = %d active (Parts A and B) + %d only in comments (Part C).' % (len(raw), len(active_all), len(only_c)))
    # checks + appendix
    import subprocess
    now = subprocess.run(['date', '-u'], capture_output=True, text=True).stdout.strip()
    ver = subprocess.run(['python3', 'verify.py'], capture_output=True, text=True).stdout.strip()
    w('')
    w('## Checks (script output)')
    w('')
    w('Generated: %s (`date -u`).  Declaration indexes: RBM3D `main` %d declarations (`decls.py RBM3D`, worktree `t/T2001` before the probe), RBM2D `c9a24cf` %d declarations (`decls.py RBM2D`).' % (now, len(RD.D3), len(RD.D2)))
    w('')
    w('`python3 verify.py` (every Lean citation of Part A, RBM3D by file:line grep in the worktree, RBM2D by `git -C ../RBM2D --no-optional-locks grep -n -E "(theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque) " c9a24cf -- <file>`):')
    w('')
    w('```')
    w(ver)
    w('```')
    w('')
    ps = subprocess.run(['python3', 'propscan.py'], capture_output=True, text=True).stdout.strip()
    w('')
    w('`python3 propscan.py` (merged theorems/defs of RBM3D `main` whose signature mentions an unproved Prop; used for the old-mode classification in the prove report):')
    w('')
    w('```')
    w(ps)
    w('```')
    w('')
    w('## Appendix: the scripts (run in one directory: `python3 decls.py RBM3D > decls3d.tsv`; the same on the RBM2D snapshot > `decls2d.tsv`; `python3 emit.py out.md`; `python3 verify.py`)')
    w('')
    w('`mapping.py` is the hand-written input (gate, scope, class, Lean and RBM2D names per row); its content is the table above.')
    for fn in ['decls.py', 'graph2.py', 'elab.py', 'render.py', 'emit.py', 'verify.py', 'propscan.py', 'gaps.py']:
        w('')
        w('### `%s`' % fn)
        w('')
        w('```python')
        w(open(fn, encoding='utf8').read().rstrip('\n'))
        w('```')
    bad = subprocess.run(['python3', 'ba_density.py'], capture_output=True, text=True).stdout.strip()
    w('')
    w('## Appendix B: numerical check behind paper-delta candidate T2001c (BA density of states differs from the semicircle)')
    w('')
    w('`python3 ba_density.py` (script below; output as printed at the generation time above):')
    w('')
    w('```')
    w(bad)
    w('```')
    w('')
    w('```python')
    w(open('ba_density.py', encoding='utf8').read().rstrip('\n'))
    w('```')
    open(outpath, 'w', encoding='utf8').write('\n'.join(L) + '\n')
    return allrows, nTot, len(partA_labels), nB

def graph2_rows(): return RD.rows
def graph2labels(): return RD.labels
def graph2sections(): return RD.sections
def owner_of(f, ln):
    o = RD.owner[(f, ln)]
    return o[0] if o else ''

if __name__ == '__main__':
    out = sys.argv[1] if len(sys.argv) > 1 else 'coverage_draft.md'
    rows_, nTot, nA, nB = main(out)
    print('written', out, len(rows_), 'rows;', nTot, 'labels;', nA, 'A;', nB, 'B')
```

### `verify.py`

```python
#!/usr/bin/env python3
"""Independent check of every Lean citation of the coverage table.
RBM3D: the declaration keyword and short name stand at the cited line of the cited file in the ticket worktree.
RBM2D: `git -C ../RBM2D --no-optional-locks grep -n` on the commit c9a24cf finds the declaration at the cited line."""
import sys, re, subprocess, collections
sys.path.insert(0, '.')
import mapping, render as RD
WT = '/Users/junyin/Lean_proof/RBM3D-wt/T2001'
R2 = '/Users/junyin/Lean_proof/RBM2D'
COMMIT = 'c9a24cf'
KW = r'(?:theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque)'
KW_ERE = '(theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque) '
def short(n): return n.split('.')[-1]
names3 = collections.OrderedDict(); names2 = collections.OrderedDict()
for m in mapping.ROWS + mapping.PSEUDO:
    for n in m['lean']: names3[RD.full(n)] = 1
    for n in m['r2d']: names2[RD.full(n)] = 1
bad3 = []; ok3 = 0
for n in names3:
    f, ln, kind, priv, name, sig = RD.IDX3[n]
    line = open(WT + '/' + f, encoding='utf8').read().split('\n')[int(ln) - 1]
    if re.search(r'\b' + KW + r'\s+' + re.escape(short(n)) + r'(?![\w.])', line) or (kind == 'instance'):
        ok3 += 1
    else:
        bad3.append((n, f, ln, line.strip()[:80]))
print('RBM3D citations: %d distinct declarations, %d verified at the cited file:line, %d mismatches' % (len(names3), ok3, len(bad3)))
for b in bad3: print('  MISMATCH', b)
# RBM2D via git grep, one call per file
byfile = collections.defaultdict(list)
for n in names2:
    f, ln, kind, priv, name, sig = RD.IDX2[n]
    byfile[f].append((n, int(ln)))
ok2 = 0; bad2 = []
for f, items in byfile.items():
    out = subprocess.run(['git', '-C', R2, '--no-optional-locks', 'grep', '-n', '-E', KW_ERE, COMMIT, '--', f],
                         capture_output=True, text=True).stdout.split('\n')
    found = {}
    for l in out:
        m = re.match(r'^' + COMMIT + r':' + re.escape(f) + r':(\d+):(.*)$', l)
        if m: found[int(m.group(1))] = m.group(2)
    for n, ln in items:
        txt = found.get(ln, '')
        if re.search(r'\b' + KW + r'\s+(?:\S*\.)?' + re.escape(short(n)) + r'(?![\w.])', txt):
            ok2 += 1
        else:
            bad2.append((n, f, ln, txt.strip()[:80]))
print('RBM2D citations: %d distinct declarations in %d files, %d verified by git grep -n at c9a24cf, %d mismatches' % (len(names2), len(byfile), ok2, len(bad2)))
for b in bad2: print('  MISMATCH', b)
```

### `propscan.py`

```python
import re
# merged declarations (theorem/def/abbrev) whose signature mentions a borrowed/owed Prop, from the declaration index of RBM3D main
props = ['ThetaDecayShort', 'ThetaDecay', 'ThetaDiffOne', 'ThetaDiffTwo', 'ThetaZeroMode', 'PropTH', 'KTreeRep', 'KLoopBound', 'TwoLoopBounded']
rows = [l.rstrip('\n').split('\t') for l in open('decls3d.tsv')]
for p in props:
    hits = []
    for f, ln, kind, priv, name, sig in rows:
        if kind not in ('theorem', 'def', 'abbrev'): continue
        if name.endswith('.' + p): continue
        if re.search(r'(?<![A-Za-z_.])' + re.escape(p) + r'(?![A-Za-z_])', sig):
            hits.append(name.replace('RBM.', ''))
    print('%-16s %d %s' % (p, len(hits), ' '.join(hits)))
```

### `gaps.py`

```python
#!/usr/bin/env python3
"""Gap list of the prove report: a partition of all non-(i) rows with a gate, printed as markdown table rows."""
import sys, collections
sys.path.insert(0, '.')
import mapping
cls = {m['id']: m['cls'] for m in mapping.ROWS + mapping.PSEUDO}
gate = {m['id']: m['gate'] for m in mapping.ROWS + mapping.PSEUDO}
G = [
 ('F0', ['eq:defmzsc#integral', 'defi:ofB#BtBt'], 'integral form of `m`; `𝓑_{η_t,K} ≍ W^{-d}B_{t,K/W}`'),
 ('F0', ['representativeL', 'def_Theta'], 'l¹ block distance (D2); band-only Θ (BA matrix `M^{(σ1,σ2)}`)'),
 ('MD', ['MBM', 'def_flow', 'Def:G_loop', 'def_Green', 'zztE#law', 'def_G0t', 'eq:opS'], '`H_t` absent: `Gsig`/`gloop` read the time-1 `Hmat`; the law identity of `zztE`; `M_t`'),
 ('MD', ['bandcw0', 'eq:blockIa'], 'one `Gauss.P` per size: no sequence, no common space for `StochDom`, no fine-lattice geometry'),
 ('MD', ['lem:SE_basic', 'Def:oper_loop', 'eq:defMzsc'], 'loop hierarchy (grid walk, DECISIONS 7), single-edge cut, `M=mI`'),
 ('PT', ['lem_propTH#5a', 'lem_propTH#5b', 'lem_propTH#6', 'lem_propTH#7', 'lem_propTH#8'], 'Props with (g,m)-dependent constants: need g- and E-uniform statements and d≥3 proofs'),
 ('KL', ['eq_Ward0', 'eq_Ward', 'lem_WI_K', 'lem_wardineq_K'], 'Ward identities: no declaration on main'),
 ('KL', ['ML:Kbound', 'tree-representation#n>=4', 'lem_pureloop#n>=4'], '`KLoopBound`, `KTreeRep` are Props; general n'),
 ('KL', ['Kn2sol', 'Kn3sol', 'tree-representation#n<=3', 'Def_Ktza', 'f-external', 'def:canpnical_part', 'lem_pureloop#n<=3'], '`TwoLoopBounded`; band-only M-loop; only the + charge; explicit solutions n≤3'),
 ('EK', ['lem:sum_decay'], 'cases 1-5 (W^{C_nε}); only kernel ingredients, conditional on `ThetaDecay` (fixed g)'),
 ('EK', ['lem:sum_decay_nonzero', 'DefTHUST'], '`hmi` excludes charge -, g-dependent constants, band only'),
 ('ST', ['ML:GLoop', 'ML:GLoop_expec', 'ML:GtLocal', 'lem:main_ind', 'lRB1', 'Gtmwc', 'Gt_bound_flow', 'Gt_avgbound_flow', 'Eq:Gdecay_w', 'Eq:LGxb', 'Eq:L-KGt-flow', 'Eq:Gdecay_flow', 'Eq:Gdecay+s<g_flow', 'Eq:Gtlp_exp_flow'], 'the whole induction and its six step statements'),
 ('ST', ['eq_L-Keee', 'DefKsimLK', 'def_ELKLK', 'Sol_CalL', 'def:CALE', 'lem:DIfREP', 'LK_simple', 'defCALJ', 'lem: EMn2_N', 'ygdhmsgq0', 'ygdhmsgq'], 'hierarchy, Duhamel with stopping time, grid path + Azuma/Doob (DECISIONS 7), martingale and contract inequalities'),
 ('ST', ['lem_GbEXP', 'lem_ConArg', 'awi2iks', 'lem:newKLK', 'eq:opt_L2', 'eq:simpleboundK', 'eq:Gronwall_dervJuD', 'eq:def2_stopping', 'Gronwall_inequality'], 'Steps 1-2 for d≥3 (J-Gronwall with stopping time, `lem:newKLK`); Gronwall is in Mathlib'),
 ('ST', ['def:XiL', 'def:XIL-K', 'lem:SEforLn', 'Def_decay', 'lem_decayLoop', 'lem:STOeq_NQ', 'Def:QtPt', 'lem_+Q', 'lem:STOeq_Qt', 'lem:iterations', 'lem: newPQ', 'lem:STOeq_Qt_nonzero'], 'Steps 3-4 for d≥3: sum-zero and zero-mode removal, new time intervals'),
 ('ST', ['lem;CLT', 'lem_dec_calE', 'TailtoTail', 'lem:pf_step5', 'lem:improve_exp_aver'], 'Step 5 CLT cancellation (d≥3), Step 6'),
 ('LW', ['lem:LWterm', 'lem: EWGn2_N', 'lem:LWterm_EXP', 'lem:LW_moment', 'lem:LW_moment_exp', 'lem:LW_moment_exp_far', 'lem:LW_moment_exp_near'], 'the light-weight estimates'),
 ('LW', ['def_graph1', 'ValG', 'def_poly', 'defnlvl0', 'dot-def', 'def scaling', 'def scaling order', 'deflvl1', 'def: BM2', 'def_auxgraph', 'strat_local'], 'graph vocabulary; main has counters-only `ord`'),
 ('LW', ['ssl', 'Oe14', 'T eq0', 'lvl1 lemma', 'lem:localregular', 'eq:Gbyxi2', 'GtoAG', 'lem:Anp', 'lem:Anp_key', 'lem:Anp_key_gh'], 'expansions and graph bounds; main has only `∂G_ij/∂h` and the Gaussian IBP'),
 ('MA', ['MR:decol', 'MR:locSC', 'MR:QUE', 'MR:QuDiff', 'eq:ukx', 'ssfa2', 'ssfa2_deter', 'eq:BetaK', 'eq:spectral_domain', 'eq:calBetaK', '[net]'], 'endpoints and their derivations; the net lemma on main is one-parameter, not for z in `D_{κ,ε}`'),
 ('UN', ['Thm: B_Univ', '[Thm2.4-proof]'], 'Green-function comparison, LSY Thm 2.2 (authorized), QUE at ε₀=𝔡/3, c=𝔡/6'),
 ('BA', ['self_m', 'def_G0', 'MR:decol_BA', 'bandcwV', 'eq:H_blocka', 'eq:Psi3D', 'eq:spectral_domainBA', 'zztE_BA'], 'BA model, `m(z,g)`, `e_g`; T2001c, T2001d, T2001g'),
 ('BA', ['lem:propM', 'lem_GbEXP_BA', 'lem_ConArg_BA', 'lem:main_ind_BA'], 'BA induction, Combes-Thomas'),
 ('BA', ['m-loop-tsp', 'M-graph-value-definition', 'tree-representation_BA', 'def_atom', 'defn_normalBA', 'def scalingBA', 'lanlw', 'lem_lweight', 'GGGamma'], 'BA M-loop trees and graph expansions'),
]
want = {i for i in cls if cls[i] != 'i' and gate[i] != '-'}
got = [i for _, ids, _ in G for i in ids]
dup = [k for k, v in collections.Counter(got).items() if v > 1]
assert set(got) == want and not dup, (sorted(want - set(got)), sorted(set(got) - want), dup)
gg = {g: gate[i] for g, ids, _ in [(0, [], 0)] for i in []}
for g, ids, _ in G:
    assert all(gate[i] == g for i in ids), (g, [i for i in ids if gate[i] != g])
if __name__ == '__main__':
    for g, ids, miss in G:
        by = collections.OrderedDict()
        for i in ids: by.setdefault(cls[i], []).append(i)
        rows = '; '.join('%s: %s' % (c, ', '.join('`%s`' % i for i in l)) for c, l in sorted(by.items(), key=lambda kv: -len(kv[0])))
        print('| %s | %s | %s |' % (g, rows, miss.replace('|', '\\|')))
    print('# rows listed: %d = non-(i) rows with a gate' % len(got), file=sys.stderr)
```

## Appendix B: numerical check behind paper-delta candidate T2001c (BA density of states differs from the semicircle)

`python3 ba_density.py` (script below; output as printed at the generation time above):

```
g=0.0  E=0: rho_N=0.31829  rho_sc=0.31831  ratio=1.0000
g=0.1  E=0: rho_N=0.30939  rho_sc=0.31831  ratio=0.9720
g=0.5  E=0: rho_N=0.21216  rho_sc=0.31831  ratio=0.6665
g=1.0  E=0: rho_N=0.13070  rho_sc=0.31831  ratio=0.4106
```

```python
import numpy as np
# BA model (d = 3): free convolution of the semicircle law (variance 1) with the spectral measure of g*Psi^(B)
# on the torus Z_L^3, L = 40: solve m = mean(1/(g*lam - z - m)), z = E + 1e-4 i, and print rho_N(E)/rho_sc(E).
L = 40
c = 2*np.cos(2*np.pi*np.arange(L)/L)
lam = (c[:, None, None] + c[None, :, None] + c[None, None, :]).ravel()   # eigenvalues of Psi^(B)
def rho_N(E, g, eta=1e-4, iters=4000):
    z = E + 1j*eta
    m = 1j
    for _ in range(iters):
        m = 0.5*m + 0.5*np.mean(1.0/(g*lam - z - m))
    return m.imag/np.pi
rho_sc = lambda E: np.sqrt(max(4 - E*E, 0))/(2*np.pi)
for g in [0.0, 0.1, 0.5, 1.0]:
    print("g=%.1f  E=0: rho_N=%.5f  rho_sc=%.5f  ratio=%.4f" % (g, rho_N(0.0, g), rho_sc(0.0), rho_N(0.0, g)/rho_sc(0.0)))
```
