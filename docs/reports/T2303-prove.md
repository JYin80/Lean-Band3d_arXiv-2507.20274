Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 02:12:54 UTC 2026

Scripts (Python, no Lean; scratch dir `T2303/`; `mc2.py`, `val.py`, `bagraph.py` are the T2295 scripts copied unchanged; `det.py` is new). Paper: `B_graphical_lemmas.tex:359-387` (`eq:BE`, `eq:LW`), `1_2_Intro_model_result.tex:658-664` (`def:Theta_BA`).

### (i) Exponent table (no exponents; the targets depend on the constants below)

| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | `t` | `0 ≤ t < 1` | `Im z_t = (1-t) Im m > 0` (G exists); `IsUnit(1-M⁺S)` needs row abs-sum of `M⁺S` `< 1` | `t=1/2`: row abs-sum `0.5000`, Gershgorin margin `1.0273` (W=1), `0.5655` (W=2); `t=0.9`: `0.9000`, margin `0.2180 ≥ 1-t=0.1`; `t=0`: branch `S=0`, `Ǧ=0`, both sides `0` |
| 2 | `L`, `W` | `3 ≤ L`, `W ≥ 1` | `3 ≤ L` only through `lwStein_sum_svarF_row … (sz.three_le_L n)` in `lwS_row_sum` (`LWStein.lean:1216`); no `L`–`W` relation | `L=3` (slack 0, allowed); `W=1` and `W=2` run |
| 3 | `g₀`, `E`, `m` | `g₀,E` any reals; `BASelf d L g₀ E m` | `m` the fixed point of `(self_m)`; `Im(E+m) ≠ 0` | `g₀=.5, E=.3`: `m=-0.139326+0.723352i`, residual `3.4e-16`; wrong `m+0.15i`: `lweight` diff/se `28.9` (Command B) |
| 4 | row sum of `S` | `Σ_β S_{αβ} = t` | `svarF = W^{-d} SBR(..)` (`FineModel.lean:47-48`), `sbKernelR 0 = 1(x=0) + g²·(…)` (`Defs/Block.lean:73-75`), so `W^{-d}1([α]=[β])` at `g=0`; row sum via `lwS_row_sum` (`LWStein.lean:1215`); `BAlwS = t·svarF` | `max|rowsum(S)-t| = 0.0e+00` |
| 5 | fine Ward row | `Σ_α |M_{xα}|² = 1` | `BAMres_fine_apply` (`FlowPins.lean:100`) + `BAMB_row_sq_real` (`Ward.lean:125`), needs `BASelf` | `6.7e-16` (W=1), `1.3e-15` (W=2) |
| 6 | symmetry | `M_{αx} = M_{xα}` | `BAMB_symm` (`Ward.lean:83`) through the fine restriction | `3.7e-16`, `2.8e-16` |
| 7 | Gershgorin (W2) | `Σ_β |(M⁺S)_{xβ}| ≤ t Σ_α|M_{xα}|² = t < 1`; `|1-a_kk| - Σ_{j≠k}|a_kj| ≥ 1-t` | `det_ne_zero_of_sum_row_lt_diag`; `M⁺S` is NOT diagonal (702 off-diagonal entries at W=1 with `g₀=.5`) | max row abs-sum `= t` (the bound `≤ t` is attained); margin `≥ 1-t` |
| 8 | solve (W1) | `v = W R`, `W = (1-M⁺S)⁻¹ = 1 + M⁺S⁺`, `S⁺ = S W` | `W(1-M⁺S)=1` | `max|W(1-M⁺S)-1| = 8.9e-16 / 1.8e-14`; `max|(1+M⁺S⁺)-W| = 1.0e-15 / 1.3e-14` |
| 9 | derivative-term coefficient (M4) | `+Γ.coeff` (`LGraph.dTerm`, `LWStein.lean:1381`, has `-Γ.coeff`) | `-` of `lanlw` cancels `-` of `∂G=-GG` | `+`: error `1.01e-09`; `-`: `3.18e+01` (Command C) |
| 10 | stopping constant | file ≤ 1500 lines at a section boundary | ticket's stop rule | ticket estimate `950 / 1180 / 1550` (not recomputed) |
| 11 | §29 | (1) `0 ≤ t < 1` present; (2) no gate; (3) only `3 ≤ L`; (4) no `∀ n`; (5) `PF d L W 0` only; (6) no hypothesis on `g₀`,`E` beyond `BASelf` (necessary, row 3); (7) no constants | | |

External hypotheses: none. `gaussIBP` is the merged theorem `RBM.Green.gaussIBP` (`IBPPoly.lean:305`), `BASelf` is a hypothesis on the data (satisfied below), so there is no limit to compute.

Definition table (`BAExpand.lean`): `M` = `BAlwM` `:64`; `M⁺_{xy}=M_{xy}M_{yx}` = `BAlwMp` `:78`; `S` = `BAlwS` `:75`; `1+M⁺S⁺ = (1-M⁺S)⁻¹` = `BAlwW` `:82` (`Ring.inverse`), `S⁺ = S·BAlwW` = `Sp` of `BAlwData`; `Ǧ` = `BAlwGc` `:71`; `G` = `BAlwG` `:67`; `f` = `BAlwf` `:86`; `∂_{h_{βα}}f` = `BAlwdf β α` `:90`; `=_𝔼` = `∫ … ∂(PF d L W 0)`.
Note: `eq:def-Spm`/`def:Theta_BA` define `S⁺` at block level with `Θ^{(+,+)}=(1-M^{(+,+)}S^{(B)})⁻¹` and no `t`; the Lean `S⁺ = S(1-M⁺S)⁻¹` (fine lattice, `S=tS_0`) is the reading that (W1) forces (Command B `lweight` rows); the pin states `BAlwW` explicitly, so no hypothesis depends on this reading.

### (ii) One concrete nondegenerate instance

`d=3, L=3, W=1, N=27, g₀=1/2, E=0.3, t=1/2, m=-0.139326+0.723352i`; also `W=2` (`N=216`), `t=0.9`, `t=0`, and `g₀=0,E=0,m=i,t=1/2` (the ticket's (I6) data). Hypotheses of `baLweight_holds`/`baW_isUnit`/`baM_row_sq`: `3 ≤ L`, `0 ≤ t < 1`, `BASelf` (res `3.4e-16`), arbitrary `P`, `x`; `lanlw` input `BAExpand_integral` merged.

Command A (`python3 det.py`):
```
d=3 L=3 W=1 N=27 g0=0.5 E=0.3 t=0.5 m=-0.139326+0.723352j Im m=0.7234 BASelf-res=3.4e-16
   |M_xx-m|max=3.6e-16  |M-M^T|max=3.7e-16  max|sum_a|M_xa|^2-1|=6.7e-16  max|rowsum(S)-t|=0.0e+00
   max row abs-sum(M^+S)=0.500000 (t=0.5); Gershgorin margin min_k(|1-a_kk|-sum_(j!=k)|a_kj|)=1.0273; |det(1-M^+S)|=4.650e+02
   max|W(1-M^+S)-1|=8.9e-16  max|(1+M^+S^+)-W|=1.0e-15  offdiag(M^+S) nonzero entries=702
d=3 L=3 W=2 N=216 g0=0.5 E=0.3 t=0.5 m=-0.139326+0.723352j Im m=0.7234 BASelf-res=3.4e-16
   |M_xx-m|max=5.8e-16  |M-M^T|max=2.8e-16  max|sum_a|M_xa|^2-1|=1.3e-15  max|rowsum(S)-t|=0.0e+00
   max row abs-sum(M^+S)=0.500000 (t=0.5); Gershgorin margin min_k(|1-a_kk|-sum_(j!=k)|a_kj|)=0.5655; |det(1-M^+S)|=4.650e+02
   max|W(1-M^+S)-1|=1.8e-14  max|(1+M^+S^+)-W|=1.3e-14  offdiag(M^+S) nonzero entries=46440
d=3 L=3 W=2 N=216 g0=0.5 E=0.3 t=0.9 m=-0.139326+0.723352j Im m=0.7234 BASelf-res=3.4e-16
   |M_xx-m|max=5.8e-16  |M-M^T|max=2.8e-16  max|sum_a|M_xa|^2-1|=1.3e-15  max|rowsum(S)-t|=0.0e+00
   max row abs-sum(M^+S)=0.900000 (t=0.9); Gershgorin margin min_k(|1-a_kk|-sum_(j!=k)|a_kj|)=0.2180; |det(1-M^+S)|=2.906e+04
   max|W(1-M^+S)-1|=2.3e-14  max|(1+M^+S^+)-W|=1.9e-14  offdiag(M^+S) nonzero entries=46440
d=3 L=3 W=1 N=27 g0=0.5 E=0.3 t=0.0 m=-0.139326+0.723352j Im m=0.7234 BASelf-res=3.4e-16
   |M_xx-m|max=3.6e-16  |M-M^T|max=3.7e-16  max|sum_a|M_xa|^2-1|=6.7e-16  max|rowsum(S)-t|=0.0e+00
   max row abs-sum(M^+S)=0.000000 (t=0.0); Gershgorin margin min_k(|1-a_kk|-sum_(j!=k)|a_kj|)=1.0000; |det(1-M^+S)|=1.000e+00
   max|W(1-M^+S)-1|=0.0e+00  max|(1+M^+S^+)-W|=0.0e+00  offdiag(M^+S) nonzero entries=0
d=3 L=3 W=1 N=27 g0=0.0 E=0.0 t=0.5 m=0.000000+1.000000j Im m=1.0000 BASelf-res=0.0e+00
   |M_xx-m|max=0.0e+00  |M-M^T|max=0.0e+00  max|sum_a|M_xa|^2-1|=0.0e+00  max|rowsum(S)-t|=0.0e+00
   max row abs-sum(M^+S)=0.500000 (t=0.5); Gershgorin margin min_k(|1-a_kk|-sum_(j!=k)|a_kj|)=1.5000; |det(1-M^+S)|=5.682e+04
   max|W(1-M^+S)-1|=0.0e+00  max|(1+M^+S^+)-W|=1.1e-16  offdiag(M^+S) nonzero entries=0
```

Command B (`python3 mc2.py 3 3 1 200000 11` and `python3 mc2.py 2 3 2 100000 11`, Monte Carlo of `lem_lweight` with `1+M⁺S⁺=(1-M⁺S)⁻¹`; case A `x=y=a=b=c=d=0`, case B `x=0,y=1,a=1,b=0,c=1,d=0`; `f1=G_ab`, `f2=G_ab conj(G_cd)`; filtered `grep -E "^d=|correct m +case [AB] f[12] lweight|wrong m.*case A f1 lweight"`; the same run also contains the `lanlw` rows, all diff/se ≤ 1.3):
```
d=3 L=3 W=1 N=27 g0=0.5 E=0.3 t=0.5: m=-0.139326+0.723352j, self_m residual=3.4e-16, max|M_xx-m|=3.6e-16, max|rowsum(S)-t|=0.0e+00
  correct m         case A f1 lweight              |diff|=1.50e-03 se=1.46e-03 |E LHS|=7.12e-02 sig=  48.7 diff/se=  1.0
  correct m         case A f2 lweight              |diff|=7.76e-04 se=1.21e-03 |E LHS|=9.94e-02 sig=  82.2 diff/se=  0.6
  correct m         case B f1 lweight              |diff|=2.61e-04 se=3.65e-04 |E LHS|=1.39e-02 sig=  38.0 diff/se=  0.7
  correct m         case B f2 lweight              |diff|=7.99e-05 se=9.59e-05 |E LHS|=6.01e-03 sig=  62.7 diff/se=  0.8
  wrong m (+0.15i)  case A f1 lweight              |diff|=3.28e-02 se=1.13e-03 |E LHS|=2.60e-02 sig=  22.9 diff/se= 28.9
d=2 L=3 W=2 N=36 g0=0.5 E=0.3 t=0.5: m=-0.032366+0.728252j, self_m residual=4.2e-16, max|M_xx-m|=5.6e-16, max|rowsum(S)-t|=0.0e+00
  correct m         case A f1 lweight              |diff|=7.33e-04 se=7.10e-04 |E LHS|=2.47e-02 sig=  34.7 diff/se=  1.0
  correct m         case A f2 lweight              |diff|=6.35e-04 se=5.47e-04 |E LHS|=2.44e-02 sig=  44.7 diff/se=  1.2
  correct m         case B f1 lweight              |diff|=3.18e-04 se=2.51e-04 |E LHS|=8.51e-03 sig=  33.9 diff/se=  1.3
  correct m         case B f2 lweight              |diff|=6.18e-05 se=7.93e-05 |E LHS|=1.83e-03 sig=  23.1 diff/se=  0.8
  wrong m (+0.15i)  case A f1 lweight              |diff|=2.63e-02 se=6.06e-04 |E LHS|=1.61e-02 sig=  26.5 diff/se= 43.5
```

Command C (`python3 val.py 1`, `python3 val.py -1`; 40 random (graph, data) pairs, `N=3`, `f` = value of `Γ-e`, `∂f` by finite differences; sum of the term graphs of (M4) vs `BAlanlwR`):
```
derivative coefficient = +1 * Gamma.coeff; 41 derivative terms (19 red edges differentiated) in 40 random (graph, data) pairs, N=3: max |RHS_direct - sum of term-graph values| = 1.01e-09 (max |RHS| = 5.49e+01); FD step 1e-5
derivative coefficient = -1 * Gamma.coeff; 41 derivative terms (19 red edges differentiated) in 40 random (graph, data) pairs, N=3: max |RHS_direct - sum of term-graph values| = 3.18e+01 (max |RHS| = 5.49e+01); FD step 1e-5
```

Command D (orientation of (M4), Lean check text vs the verified script; `grep -n` on `docs/tickets/checks/T2303-check.lean:277-290` and `bagraph.py` `lanlwD`): Lean blue `owxDE β α e` = `(src,β),(α,dst)`, red = `(src,α),(β,dst)` (`LWWeightExp.lean:468-471`), plus `G_{βy}` = `⟨true,false,β,y⟩`, waved `⟨false,true,α,β⟩`, mdot `⟨true,x,α⟩`, `c=1` (coefficient `+Γ.coeff`); script `de=[(T,F,a,be),(T,F,al,b)] if blue else [(F,F,a,al),(F,F,be,b)]`, `(T,F,be,y)`, `(F,T,al,be)`, `(T,x,al)`, `coeff=g[coeff]`: same.

### (iii) Against the paper, §29, two data one model, consumers

- `BAlweightR` is `eq:LW` (`B:376-387`) term by term: `Σ_y (1+M⁺S⁺)_{xy}( Σ_{α,β} M_{yα}S_{αβ}Ǧ_{αy}Ǧ_{ββ}f − Σ_{α,β} M_{yα}S_{αβ}G_{βy}∂_{h_{βα}}f )` with `M⁺_{xy}=M_{xy}M_{yx}` (`B:388`): PASS. (M4) is `eq:BE` (`B:361`) term by term, derivative coefficient `+Γ.coeff`: PASS (Command C: `1.01e-09` vs `3.18e+01`; orientation, Command D).
- (W1) route: `lanlw` at `(y,y)` gives `v_y = Σ_β (M⁺S)_{yβ}v_β + R_y` (uses `G_{αy}=M_{αy}+Ǧ_{αy}`, `M_{yα}M_{αy}=M⁺_{yα}`), so `v = (1-M⁺S)⁻¹R`, then row `x`. Needs exactly `lanlw` at the model (same `m`, same `M` in `M⁺`) and `IsUnit(1-M⁺S)`; (W2) needs `BASelf` at real `E` (`BAMB_row_sq_real`): "two data, one model" PASS (`lweight` diff/se `1.0, 0.6, 0.7, 0.8` correct `m`, `28.9` wrong `m`).
- Consumers: BA-L2c needs `lanlwTerms`, `lanlw_val` for `Ǧ_{xy}` with `f ↦ Ǧ_{y'x}f` and `BAlwW`: the `lanlw_val` shape (any `Γ`, any `p ∈ lwSplit Γ.solid` with `σ = circ = true`, any external labelling) covers it; BA-L3 `B:407-410` needs the counters of T2315 on exactly the check §3 texts (not here). Stale item (2) (graph operation of `lem_lweight`) is in no target here, as the ticket decides (§129 (2)).
- `t = 0` (W3): `Ǧ = 0` (`BAExpand_Gc_zero`), `S = 0`: every term of `lanlwTerms` has a waved factor `S_{αβ}`, so RHS `= 0 = ` LHS (the factor `Ǧ_{xy}` of `p.1`); consistent with `det.py` row `t=0` (`M⁺S = 0`, `W = 1`).

### Verdicts

- Target 1 (`BAlweight`: pin, `baM_row_sq`, `baM_symm`, `baW_isUnit`, `baW_mul`, `baLweight_holds`): PASS. Hypotheses hold at the instance, `IsUnit(1-M⁺S)` with margin `≥ 1-t`, MC agreement `≤ 1.3` s.e.
- Target 2 (graph vocabulary `BAlwData`, `lanlwExt`, `lanlwT1`, `lanlwD`, `lanlwTerms`): PASS (orientation and coefficient match the verified script).
- Target 3(b) (`lanlw_val`): PASS at the level of mathematics (Command C; `t = 0` branch above). 3(c) is T2315's and not assessed here.
- Instances (I5), (I6): PASS (`g₀=0,E=0,m=i,t=1/2`: `M=i·1`, `M⁺S=-S`, `1-M⁺S = 3/2·1`, margin `1.5000`, `BASelf` residual `0`).

## (b) Script output (evidence run `date -u`: Thu Oct  8 02:46:52 UTC 2026; worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2303`)
$ git log --oneline main..t/T2303; git diff --stat main...t/T2303 | tail -1; git status --short | wc -l; grep -cE 'sorry|admit|native_decide|axiom' RBM3D/Graph/BAExpandW.lean
```
faea938 T2303: baM_symm unconditional (Psi symmetric), docstring cites
1c5d6fc T2303: BA-L2b1 weight expansion lem_lweight (baLweight_holds) and lanlw as a graph operation (lanlw_val)
 1 file changed, 1066 insertions(+)
       0
0
```
$ lake build RBM3D.Graph.BAExpandW 2>&1 | grep -E 'BAExpandW|Build completed|error'; lake build 2>&1 | tail -1   (full library; root RBM3D.lean does not import the new module yet)
```
Build completed successfully (3779 jobs).
Build completed successfully (4123 jobs).
```
$ line count, then section headings with their line numbers (file lengths at the section boundaries: 149, 440, 964, 1063)
```
    1066
57:/-! ## 1. The pin and the vocabulary (copied verbatim from the check file, sections 2 a
90:/-! ## 3. `lanlw` as a graph operation: vocabulary (copied verbatim) -/
150:/-! ## 4. Target 1: the weight expansion -/
441:/-! ## 5. `lanlw` as a graph operation: the value identity (`lanlw_val`)
965:/-! ## 6. Instance graphs and compiled instances (namespace `RBM.Graph.BAExpandWInst`)
1064:end RBM.Graph
```
$ lake env lean ax.lean   (one `#print axioms` for each of the 34 new public declarations, grouped by axiom set; prefix `RBM.Graph.` dropped)
```
[propext, Classical.choice, Quot.sound] (33):
  BAlweightL BAlweightR BAlweight BAlwData BAGraph.lanlwExt BAGraph.lanlwT1 BAGraph.lanlwD BAGraph.lanlwTerms baM_symm baM_row_sq baW_isUnit baW_mul
  baLweight_holds BAExpandW_sampleData BAExpandW_sedge_val_blue BAExpandW_sedge_val_red BAExpandW_sedge_val_tame1 BAExpandW_dh_sedge_val
  BAExpandW_baPoly_edgePoly BAExpandW_baPoly_edgePoly_prod BAExpandW_K BAExpandW_term_eq BAExpandW_term_tame1 BAExpandW_lanlwExt_term
  BAExpandW_lanlwT1_term BAExpandW_lanlwD_term BAExpandW_term_integral BAExpandW_integral_val2 BAExpandW_lanlw_val_seq lanlw_val baGcxy baGcxx
  BAExpandWInst.baLweight_t0
[propext, Quot.sound] (1):
  BAExpandW_lab2_emb
```
$ sed -n 82,86p BAExpandW.lean (the pin); extract.py (signatures of the six theorems, `[line]`); grep of the definitions of target 2 and the pin
```
def BAlweight (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (E : ℂ) m →
    0 ≤ t → t < 1 →
    ∀ (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) (x : Idx d L W),
      ∫ ω, BAlweightL d L W g0 E t m P x ω ∂(PF d L W 0) = ∫ ω, BAlweightR d L W g0 E t m P x ω ∂(PF d L W 0)
[187] theorem baM_symm (g0 E : ℝ) (m : ℂ) (x α : Idx d L W) :
    BAlwM d L W g0 E m x α = BAlwM d L W g0 E m α x := by
[198] theorem baM_row_sq (d L W : ℕ) [NeZero L] [NeZero W] (g0 E : ℝ) (m : ℂ) (h : RBM.BA.BASelf d L g0 (E : ℂ) m)
    (x : Idx d L W) : ∑ α, ‖BAlwM d L W g0 E m x α‖ ^ 2 = 1 := by
[247] theorem baW_isUnit (d L W : ℕ) [NeZero L] [NeZero W] (hL : 3 ≤ L) (g0 E t : ℝ) (m : ℂ)
    (hSelf : RBM.BA.BASelf d L g0 (E : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    IsUnit (1 - BAlwMp d L W g0 E m * Matrix.of (BAlwS d L W t)) := by
[268] theorem baW_mul (hL : 3 ≤ L) (g0 E t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (E : ℂ) m)
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    BAlwW d L W g0 E t m * (1 - BAlwMp d L W g0 E m * Matrix.of (BAlwS d L W t)) = 1 :=
[354] theorem baLweight_holds (d : ℕ) : BAlweight d := by
[908] theorem lanlw_val (d L W : ℕ) [NeZero L] [NeZero W] (hL : 3 ≤ L) (g0 E t : ℝ) (m : ℂ)
    (hSelf : RBM.BA.BASelf d L g0 (E : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1)
    {Ex Ix : Type} [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix)
    (p : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))) (hp : p ∈ lwSplit Γ.solid) (hσ : p.1.σ = true)
    (hc : p.1.circ = true) (ℓe : Ex → Idx d L W) :
    ∫ ω, Γ.val (BAlwData d L W g0 E t m ω) ℓe ∂(PF d L W 0) =
      ∫ ω, ((BAGraph.lanlwTerms Γ p).map fun Δ => Δ.val (BAlwData d L W g0 E t m ω) ℓe).sum ∂(PF d L W 0) := by
65:noncomputable def BAlweightL (x : Idx d L W) (ω : Ω d L W) : ℂ :=
70:noncomputable def BAlweightR (x : Idx d L W) (ω : Ω d L W) : ℂ :=
98:noncomputable def BAlwData (g0 E t : ℝ) (m : ℂ) (ω : Ω d L W) : BALData (Idx d L W) where
114:def BAGraph.lanlwExt (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I))) (c : ℂ)
122:def BAGraph.lanlwT1 (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : BAGraph E (I 
133:def BAGraph.lanlwD (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
144:def BAGraph.lanlwTerms (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
```
$ python3 -I checkeq.py   (check (a): sections 2 and 3 of the check file against the file, whitespace-normalized)
```
check block (sections 2+3) chars: 4697  lean block chars: 4697
EQUAL: True
section 2 text found in lean: True
section 3 text found in lean: True
```
Check (b): the check file with `import RBM3D.Graph.BAExpandW` added and these four examples appended after its last `end`:
```
example : RBM.Graph.T2303Check.T2303_baM_row_sq :=
  fun d L W _ _ g0 E m h x => RBM.Graph.baM_row_sq d L W g0 E m h x
example : RBM.Graph.T2303Check.T2303_baW_isUnit :=
  fun d L W _ _ hL g0 E t m h h0 h1 => RBM.Graph.baW_isUnit d L W hL g0 E t m h h0 h1
example : RBM.Graph.T2303Check.T2303_baLweight_holds := fun d => RBM.Graph.baLweight_holds d
example : RBM.Graph.T2303Check.T2303_lanlw_val := by
  intro d L W _ _ hL g0 E t m hS h0 h1 Ex Ix _ _ Γ p hp hσ hc ℓe
  exact RBM.Graph.lanlw_val d L W hL g0 E t m hS h0 h1 Γ p hp hσ hc ℓe
```
$ lake env lean check_b.lean; echo "exit code: $?"; grep -c error <its output>
```
exit code: 0
0
```
Compiled nonempty instances (all inside `lake build RBM3D.Graph.BAExpandW` above; `BAExpandInst.baSelf_zero` is the merged `BASelf 3 3 0 0 i`).
$ grep -n '^example\|^theorem baLweight_t0' RBM3D/Graph/BAExpandW.lean   (line numbers of `baLweight_t0` (I5 at t = 0: `0 = 0`) and of the 8 examples)
```
992 1007 1017 1028 1032 1036 1039 1044 1055 
```
$ for s in 1007 1028 1044 1055: print from line s to the next blank line   (I5 at g0 = 0, I6 baW_isUnit, lanlw_val on baGcxy and on baGcxx; the others are at 1017, 1032, 1036, 1039)
```
example :
    ∫ ω, BAlweightL 3 3 1 0 0 (1 / 2) Complex.I (MvPolynomial.X (true, (fun i => if i = 0 then 1 else 0), 0) *
        MvPolynomial.X (false, (fun i => if i = 0 then 1 else 0), 0)) 0 ω ∂(PF 3 3 1 0) =
    ∫ ω, BAlweightR 3 3 1 0 0 (1 / 2) Complex.I (MvPolynomial.X (true, (fun i => if i = 0 then 1 else 0), 0) *
        MvPolynomial.X (false, (fun i => if i = 0 then 1 else 0), 0)) 0 ω ∂(PF 3 3 1 0) :=
  baLweight_holds 3 3 1 (by norm_num) 0 0 (1 / 2) Complex.I BAExpandInst.baSelf_zero (by norm_num) (by norm_num) _ _
example : IsUnit (1 - BAlwMp 3 3 1 0 0 Complex.I * Matrix.of (BAlwS 3 3 1 (1 / 2))) :=
  baW_isUnit 3 3 1 (by norm_num) 0 0 (1 / 2) Complex.I BAExpandInst.baSelf_zero (by norm_num) (by norm_num)
example :
    ∫ ω, baGcxy.val (BAlwData 3 3 1 0 0 (1 / 2) Complex.I ω)
        ![(0 : Idx 3 3 1), fun i => if i = 0 then 1 else 0] ∂(PF 3 3 1 0) =
      ∫ ω, ((BAGraph.lanlwTerms baGcxy ⟨⟨true, true, .inl 0, .inl 1⟩, []⟩).map fun Δ =>
        Δ.val (BAlwData 3 3 1 0 0 (1 / 2) Complex.I ω)
          ![(0 : Idx 3 3 1), fun i => if i = 0 then 1 else 0]).sum ∂(PF 3 3 1 0) :=
  lanlw_val 3 3 1 (by norm_num) 0 0 (1 / 2) Complex.I BAExpandInst.baSelf_zero (by norm_num) (by norm_num)
    baGcxy _ (by simp [baGcxy, lwSplit]) rfl rfl _
example :
    ∫ ω, baGcxx.val (BAlwData 3 3 1 0 0 (1 / 2) Complex.I ω) (fun i => i.elim0) ∂(PF 3 3 1 0) =
      ∫ ω, ((BAGraph.lanlwTerms baGcxx ⟨⟨true, true, .inr 0, .inr 0⟩, []⟩).map fun Δ =>
        Δ.val (BAlwData 3 3 1 0 0 (1 / 2) Complex.I ω) (fun i => i.elim0)).sum ∂(PF 3 3 1 0) :=
  lanlw_val 3 3 1 (by norm_num) 0 0 (1 / 2) Complex.I BAExpandInst.baSelf_zero (by norm_num) (by norm_num)
    baGcxx _ (by simp [baGcxx, lwSplit]) rfl rfl _
```
$ name-clash grep (clash2.sh: `grep -rnw --include='*.lean'` of each new public name over RBM3D/, excluding Probe/ and BAExpandW.lean itself)
```
20 public names + prefix BAExpandW_/BAExpandWInst, RBM3D/ outside Probe/ and outside BAExpandW.lean: 0 hits
```
$ registry pre-check: temporary uncommitted file `import RBM3D` + `import RBM3D.Graph.BAExpandW` + `#assert_rbm_axioms`, `lake env lean`; first line; number of lines naming BAlweight/BAExpandW/BAlanlw
```
exit code: 0
axiom audit: 9006 theorems, 2935 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
0
```
$ same without the new import (so the +27 theorems / +12 definitions above are this file's)
```
axiom audit: 8979 theorems, 2923 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
```

### Narrative (stage 1b)
- Delivered, all targets of the ticket, in one file (1066 lines; commits `1c5d6fc`, `faea938` on `t/T2303`): the pin `BAlweight` and the vocabulary (check sections 2, 3: text equal, script above); target 1 (`baM_symm`, `baM_row_sq`, `baW_isUnit`, `baW_mul`, `baLweight_holds`); target 3(b) `lanlw_val`; instances (I5), (I6) and two applications of `lanlw_val`. Not here by the ticket's cut: target 3(c), instances (I3)-(I4) counters (T2315); `baGcxy`, `baGcxx` are defined (check section 4 text).
- Section (a) is not edited and no (a′) is needed: no Lean statement contradicts it. The Python scripts of (a) were not re-run.
- `baLweight_holds`: for `0 < t < 1` the merged `baLanlw_holds` at `(y, y)` (already on `PF d L W 0`) replaces a second run of `BAExpand_integral`. `BAExpandW_pathwise`: `G_{αy} = M_{αy} + Ǧ_{αy}` splits `BAlanlwR y y` into `Σ_β (M⁺S)_{yβ} Ǧ_{ββ} f` plus the bracket of `BAlweightR`; integrability of both on `PF` by `Tame` through `BAExpandW_integrable_PF` (`Sizes.seqP_map_slice`); then `v - (M⁺S) v = r`, `v = W r` by `baW_mul`. `t = 0`: both integrands vanish (`Ǧ = 0`, `S = 0`).
- `baW_isUnit`: `det_ne_zero_of_sum_row_lt_diag` for `1 - P`, `P = M⁺S`, from `Σ_β ‖P_{kβ}‖ ≤ t Σ_α ‖M_{kα}‖² = t` (`baM_symm`, `baM_row_sq`, row sums of `S` = `t` from `lwS_row_sum` at `u = 1` and `svarF_nonneg`); only `3 ≤ L`, `BASelf`, `0 ≤ t < 1`.
- `baM_symm` has no hypothesis (the ticket gives only `BAlwM x α = BAlwM α x`): `Ψ` is symmetric (`zdistD_neg` as in `PsiB_isHermitian`, `Matrix.kroneckerMap_transpose`), then `Matrix.transpose_nonsing_inv`.
- `lanlw_val`: seq-space `BAExpandW_lanlw_val_seq` from the per-labelling `BAExpandW_term_integral` (twin of `owx_term_integral`: `P` = product of `owxEdgePoly`, `BAExpand_integral`, `lwStein_dh_listProd`), the term formulas `BAExpandW_lanlwT1_term`/`_lanlwD_term`, then `lwWx_integral` (continuity from `Tame`). The check-§3 coefficient `+Γ.coeff` of `lanlwD` closes against the `-Σ M S G ∂f` of `BAExpand_integral`: sign and orientation are machine-checked by this proof. `t = 0`: `Ǧ = 0` on the left, every term of `lanlwTerms` has the waved factor `S_{αβ} = 0`.
- Own copy `BAExpandW_lab2_emb`: the merged `owxLab2_emb` carries `[Fintype E]`, which `T2303_lanlw_val` (`{Ex Ix : Type} [Fintype Ix] [DecidableEq Ix]`) does not. `baw_tame` is a local copy of the local macro `ba_tame`; helpers are `private` or `BAExpandW_`-prefixed.
- Registry: the pre-check exits 0 and names no `BAlweight`/`BAExpandW` line, so `RBM3D/Test/Axioms.lean` is unchanged (diff stat: one file). Hub: add `import RBM3D.Graph.BAExpandW` after the last `import` of `RBM3D.lean`.
- No port (no RBM1D/RBM2D file read or copied); the stop rule (over 1500 lines) never applied: 149 / 440 / 964 / 1063 lines at the section boundaries.

## (c) Verified Mathlib names (`#check` of each in a file importing the new module; `lake env lean mathlib_names.lean`)
```
present  det_ne_zero_of_sum_row_lt_diag
present  Matrix.isUnit_iff_isUnit_det
present  Matrix.one_apply_ne
present  norm_sub_norm_le
present  Matrix.transpose_submatrix
present  Matrix.kroneckerMap_transpose
present  Matrix.nonsing_inv_eq_ringInverse
present  Matrix.transpose_nonsing_inv
present  Ring.inverse_mul_cancel
present  MeasureTheory.integrable_map_measure
present  MeasureTheory.integral_finsetSum
present  MeasureTheory.integrable_finsetSum
present  Matrix.mulVec_mulVec
present  Matrix.one_mulVec
present  Matrix.sub_mulVec
present  continuous_list_sum
present  List.sum_eq_zero
present  map_list_prod
present  Equiv.sum_comp
present  Fintype.sum_prod_type
ABSENT   Matrix.transpose_kronecker  (Unknown constant)
```

## (d) Open issues and paper-delta candidates
- T2303a (candidate): the pin's `1 + M⁺S⁺` is `BAlwW = Ring.inverse (1 - M⁺S)` on the fine lattice with `S = t·svarF` (`BAlwData.Sp = S·BAlwW`); the paper defines `S⁺` through `Θ^{(+,+)} = (1 - M^{(+,+)}S^{(B)})⁻¹` at block level without `t` (Note in (a)). The pin states `BAlwW` explicitly, so no hypothesis depends on the reading.
- T2303b (candidate): `f` is a resolvent polynomial (`MvPolynomial` in the entries of `G`, `G*`), not a general "differentiable function of `G`" (`B:376-387`); inherited from the merged pins `BAlanlw`, `LWPins_resPoly`.
- T2303c (candidate): `lanlw_val` is for a blue circled edge `p.1 = Ǧ_{xy}` (`σ = circ = true`), as in the check text; the conjugate (red) case is not stated.
- Open, not in any target here: the `lem_lweight` graph operation (stale item (2) of the ticket; DECISIONS §129 (2) leaves it to BA-L3's design).
- For T2315: `lanlwTerms` lives on `BAGraph Ex (Ix ⊕ Fin 2)`; `BAExpandW_lanlwExt_term` (`.term` of `lanlwExt`) and `BAExpandW_lab2_emb` are reusable.
