Prover model: claude-sonnet-5-5
## (a) Math preflight — Sun Oct  4 07:13:29 UTC 2026
Scripts (python3+numpy, no Lean): `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2120`: `model.py` (copy of T2107's: `svarF` from `sbKernelR`, `Xentry`), `mc2.py`, `counters2.py`, `inst2.py`, `summ.py`.
Notation: `m=mE E`, `z=zt E t=E+(1-t)m`, `S=t·svarF`, `Sp=S(1-m²S)⁻¹` (`LWPins_lwSp d L W g E t`, args `g E t` as fixed by §34; `LWPins.lean:164` already has them), `Ǧ=G-m`, `∂_{αw}=∂_{h_{αw}}`, `∂_{αw}G_{ab}=-G_{aα}G_{wb}`.

### Derivation of the eight terms (`7_8:334-349`, pin `LWPins.lean:164-183`), and the map to the merged proof pattern
Row Stein at row `w`, `F_w=G_{y'w}f`, `A_w:=E[G_{wy}F_w]`.  Resolvent identity `(HG)_{wy}=δ_{wy}+zG_{wy}`; Stein `E[h_{wα}Φ]=S_{wα}E[∂_{αw}Φ]`; `Σ_αS_{wα}=t`, `z+tm=-1/m`.
Defect `Z_w:=δ_{wy}F_w+zG_{wy}F_w+Σ_αS_{wα}G_{αα}G_{wy}F_w-Σ_αS_{wα}G_{αy}∂_{αw}F_w`, `E Z_w=0` (Stein on `G_{αy}F_w`, `w` fixed), and `∂_{αw}F_w=-G_{y'α}G_{ww}f+G_{y'w}∂_{αw}f`, `G_{ww}=m+Ǧ_{ww}`.  Solving for `G_{wy}F_w`:
  `A_w = E[R_w] + m²Σ_αS_{wα}A_α - mE[Z_w]`, with `R_w = mδ_{wy}G_{y'w}f + mΣ_αS_{wα}Ǧ_{αα}G_{wy}G_{y'w}f + mǦ_{ww}Σ_αS_{wα}G_{αy}G_{y'α}f - mΣ_αS_{wα}G_{αy}G_{y'w}∂_{αw}f` (R1,R3,R5,R7 at `w`).
Resummation: with `hSp: Sp-m²SpS=S` (merged `lwWx_hSp`, from `lwSplus_spec`), `Σ_w(δ_{xw}+m²Sp_{xw})(A_w-m²(SA)_w-R_w)=A_x-R_x-m²(Sp R)_x`, so `A_x=R_x+m²Σ_αSp_{xα}R_α-mΣ_w(δ_{xw}+m²Sp_{xw})Z_w`.  Expectation: `E Z_w=0`.  Applying `R`: `m²Sp_{xα}R_α` gives R2 (`δ_{αy}` part), R4 (`Ǧ_{ββ}`), R6 (`Ǧ_{αα}`), R8 (derivative); `R_x` gives R1,R3,R5,R7.  This is the pin's eight terms in the order of `7_8:337-339` (checked by script below, including the exact per-sample identity).
Map to `owx_integral` (`LWStein.lean:1239`, `owx_defect_identity` :107): same chain (`stein_lwPoly` :1108 + resolvent identity + `hSp`), but the LHS is `G_{xy}G_{y'x}f`, not `Ǧ_{xx}f`, so `owx_integral` is not applicable; it needs (1) an off-diagonal resolvent identity `Σ_αH_{wα}G_{αy}=δ_{wy}+zG_{wy}` (merged `lwStein_resolvent_id` :1116 is diagonal only: new helper `oe2x_*`), (2) `stein_lwPoly` for the polynomial `X(α,y)·X(y',w)·P'`, (3) the algebraic defect identity above (twin of `owx_defect_identity`).  Reused from T2107 (`Graph/LWWeightExp`): `lwWx_lwG/lwS/lwSp/hSp/flow/im_pos/mE_ne`, `lwWxRename`+`lwWx_lwPoly` (`P↦P'`, red variable `(b,a,false)`), `lwWx_lwdf` (derivative, `0<t`), `lwWx_integral` (`seqP`→`PF`, `F` continuous), `lwWx_lwGc`; `lwS_row_sum` :1215.  Boundedness: `‖G‖≤1/Im z`, `Im z=(1-t)Im m>0`, so every integrand is bounded.
`t=0`: `Hflow 0 ω=0`, `S=0`, `Sp=0`, `G=(-z)⁻¹I=mI` (`zt E 0=E+m=-1/m`; script below `G(0)-mI=0`).  LHS `=m²δ_{xy}δ_{y'x}f(mI)`; RHS: R1 `=mδ_{xy}(mδ_{y'x})f` equal, R2-R8 carry a factor `S`, `Sp` or `Ǧ_{xx}=0`; no differentiability of `f` is needed.  Merged `Gres_zero_eq_scalar` is on `Vtx` (`LWWeightExp.lean:366` redoes it on `Idx`: reuse that scalar fact).

### (i) Exponent table (the pin has no exponents; thresholds and constants)
| quantity | value | constraint | slack |
|---|---|---|---|
| `|E|<2` | pin | `Im m=√(4-E²)/2>0`, `m≠0` (`lwWx_mE_ne`) | fails only at `E=±2` (outside) |
| `t<1` | pin | `Im z=(1-t)Im m>0` (`zt_im` Semicircle:182, `lwWx_im_pos`) | `→0` as `t→1`, none needed |
| `0<t` | bridge (`dhSample`, `lwWx_lwdf` need `0<u`) | `t=0` separate case | exact (above) |
| `‖m‖=1` | `norm_mE` (Semicircle:63) | `‖m‖²t<1` for `lwS_isUnit` | `1-t` |
| flow | `z+tm=E+m=-1/m` | `lwWx_flow` | residual 0 (below) |
| row sums of `S` | `t` (`lwS_row_sum`) | `Σ_αS_{xα}Ǧ_{αα}` split, `hzm` | residual 0 to 12 digits at the instance |
| `‖S‖_op`, `1-m²S` | `t`; min singular value `1.05` at the instance | unit (`lwS_isUnit`) | `1-t` |
| `hSp` | `Sp-m²SpS=S` | resummation | residual `1.4e-16` at the instance |
| `g` | only `g²` enters `svarF` (T2107 row, `checks.py`) | pin is `∀ g:ℝ`; Monte Carlo at `g=1/2` | `g≤0` covered by `S(g)=S(-g)` (T2107 output) |
| `L,W,d` | `3≤L`, `NeZero W`, any `d` | no `3≤d`, no `L`-`W` relation, no `∀ᶠ n`, no `ilambda` (§29 (2)(3)(4) not triggered) | — |
| vertex condition for the graph operation | `x` internal, `x≠y` as vertices (R1 merges `x` into `y`) | R1 `Δord=+1` needs `ΔnV=-1`; if `y=x` (weight `G_{xx}`) R1 is `ΔnS=-1,ΔnV=0`: `Δord=-1` (counters script, last line) | R2-R8: no condition (`y,y'` arbitrary, may equal `x`) |
| counters R1..R8 (`Δ(nS,nW,nV,nM)`, `Δord=ΔnS+2(ΔnW-ΔnV)`, `ord` Graph/ScalingOrder:65) | R1 `(-1,0,-1,{0,-1})`; R2 `(-1,1,0,{0,-1})`; R3,R5,R7 `(1,1,1,0)`; R4,R6,R8 `(1,2,2,0)` | `Δord=+1` for all eight (T2040 b.9 row LW-07) | `ΔnM∈{0,-1}` for R1,R2 (merging molecules), not `0` as T2040 table: candidate `T2120a`; `nM` is not in `ord` |
Counters of R7, R8: `dTerm_counters` (:1619: `nS+1`, `nW,nV,nM` same) and `dTerm_ord` (:1656), plus the relabel of the dTerm's two external vertices `(α,w)` to the new internal `α` and to `x`; `LGraph.relabel` (LWVocab:460) and `term_relabel` (:468) exist.  No definition outside `LWVocab`/`LWStein` is needed for the counters (no stop condition).

### (ii) One concrete nondegenerate instance
Lean instance (ticket): `d=3,L=3,W=1,g=1/2,E=0,t=1/2,P=1`, vertices `x=(0,0,0)`, `y=y'=(1,0,0)` (the `R2` term `0.0345` is nonzero; at distinct `y≠y'`, `E=0`, `f=1` all terms were within Monte Carlo noise of 0, so that choice would not test the identity).  Second: `W=2` (`N=216`).
`cd $S && python3 inst2.py` (verbatim):
```
instance d=3 L=3 W=1 g=0.50 E=0.0 t=0.50 N=(WL)^d=27
|E|<2: True | 3<=L: True | 0<=t<1: True | m= 1j |m|= 1.0 | Im z=0.5000
flow z+t m = 1j, -1/m = 1j
row sums of S: min 0.500000000000 max 0.500000000000 (=t) | ||S||_op=0.500000000000 | min sing(1-m^2 S)=1.0500
hSp residual max|Sp - m^2 Sp S - S| = 1.39e-16
t=0: max|G(H=0)-m I| = 0.00e+00
x=(0,0,0), y=y'=(1,0,0), P=1, 1e5 samples: E[LHS]=+0.04058-0.00037j; R1..R6 means: ['+0.0000+0.0000j', '+0.0345+0.0001j', '+0.0016+0.0000j', '+0.0006-0.0000j', '+0.0031-0.0001j', '+0.0006-0.0000j'] R7=R8=0 (df=0)
E[LHS-RHS]=+0.00013-0.00042j, SE=0.00034, |.|/SE=1.31
```
`cd $S && python3 counters2.py` (4000 random graphs: x internal, edges G_xy and G_y'x, random further solid/waved/dotted edges, y,y' arbitrary; counters re-implemented from LWVocab:157-182; verbatim):
```
random graphs: 4000, (x internal, G_xy, G_y'x blue no circ; y!=x for R1); delta (nS,nW,nV,nM,ord) -> multiplicity
R1 {(-1, 0, -1, -1, 1): 1645, (-1, 0, -1, 0, 1): 1028}
R2 {(-1, 1, 0, -1, 1): 1645, (-1, 1, 0, 0, 1): 2355}
R3 {(1, 1, 1, 0, 1): 4000}
R4 {(1, 2, 2, 0, 1): 4000}
R5 {(1, 1, 1, 0, 1): 4000}
R6 {(1, 2, 2, 0, 1): 4000}
R7 {(1, 1, 1, 0, 1): 7843}
R8 {(1, 2, 2, 0, 1): 7843}
R1 at y=x (weight G_xx removed, vertex kept): {(-1, 0, 0, 0, -1): 2000}
```
`cd $S && python3 mc2.py W E 10000` for `(W,E) ∈ {1,2}×{0,1}`, `d=3,L=3,g=1/2`, `t∈{1/2,9/10}`, `x=(0,0,0)`, `a=(1,0,0)`, `b=(0,1,0)`; configs (x,y,y') = (x,a,b), (x,x,b), (x,a,x), (x,a,a), (x,x,x); `f∈{1,G_xx}` (`∂_{αw}G_xx=-G_{xα}G_{wx}`); the eight terms R1..R8 as the pin (`Sp` the pin's); last column of `summ.py`: |mean(LHS-RHS)|/SE over 20 rows each; "pathwise" = max over samples of |(LHS-RHS)-(-mΣ_w(δ_xw+m²Sp_xw)Z_w)| (exact per-sample identity, derivation above).  `python3 summ.py` (verbatim):
```
out_W1_E0.txt: 20 (config,f,t) rows; max |LHS-RHS|/SE = 2.06; mean over rows = 1.09; max pathwise defect residual = 6.8e-13
out_W1_E1.txt: 20 (config,f,t) rows; max |LHS-RHS|/SE = 1.42; mean over rows = 0.86; max pathwise defect residual = 2.8e-12
out_W2_E0.txt: 20 (config,f,t) rows; max |LHS-RHS|/SE = 1.64; mean over rows = 0.94; max pathwise defect residual = 3.7e-15
out_W2_E1.txt: 20 (config,f,t) rows; max |LHS-RHS|/SE = 0.90; mean over rows = 0.52; max pathwise defect residual = 7.2e-15
```
Two rows of `out_W2_E1.txt` (verbatim, cut at the column shown; terms R1..R8 are in order):
```
W=2 E=1 t=0.5 y=y'     f=Gxx LHS -0.0141-0.0151j | R1..R8 +0.000+0.000j -0.014-0.016j +0.000-0.000j -0.000-0.000j -0.000+0.000j +0.000-0.000j -0.000+0.001j +0.000-0.000j | LHS-RHS +0.0000-0.0000j SE 0.0004 |diff|/SE=0.11 | pathwise |(LHS-RHS)-(-mSum(d+m2Sp)Z)|max=8.1e-16
W=2 E=1 t=0.9 x=y=y'   f=Gxx LHS +0.9296-0.0549j | R1..R8 +0.976-0.017j -0.025-0.022j +0.001+0.001j -0.000-0.000j +0.000+0.003j -0.000-0.000j -0.024-0.019j +0.000+0.001j | LHS-RHS +0.0011-0.0016j SE 0.0081 |diff|/SE=0.24 | pathwise |(LHS-RHS)-(-mSum(d+m2Sp)Z)|max=7.2e-15
```
Reading: max |diff|/SE ≤ 2.06 over 80 rows (no systematic deviation); the pathwise residual is at rounding level (≤ 2.8e-12, growing with `‖G‖` at `t=0.9`); R7, R8 are nonzero at `f=G_xx` (e.g. `-0.024-0.019j` above) and absent at `f=1`.  `∂f` for `f=G_xx` is used in both the Monte Carlo and the pathwise check; the pin's `LWPins_lwdf` is the same quantity (`lwWx_lwdf`).
No external hypothesis beyond `GaussIBP sz` (`gaussIBP sz`, merged); its limit check is T2107's.

### Verdicts
- Target 1 `lwGGExp_holds : LWggExp d` (as fixed by §34): PASS.  The pin is true as written (derivation + 80-row Monte Carlo + exact pathwise identity); `0≤t<1`, every `g`, `3≤L`, `W≥1`, `|E|<2` hold at the instance; `t=0` is exact.  New material: off-diagonal resolvent identity, algebraic defect identity (twin of `owx_defect_identity`), Stein for `X(α,y)X(y',w)P'`, integrability (bounded integrands).
- Target 2 `(Oe2x)` as a graph operation: PASS.  Eight term graphs (the `owxT*` pattern; R7, R8 via `dTerms` + relabel), `Δord=+1` for each; hypotheses to state: `x` internal, and `x≠y` as vertices for R1; `ΔnM∈{0,-1}` for R1, R2 (`=0` for R3-R8).  Paper-delta candidates: `T2120a` (T2040 b.9 table says `dM=0` for R1, R2; the counters script gives `ΔnM∈{0,-1}`); `T2120b` (R1 needs `x≠y`; with `y=x` the term is `Δord=-1`).

## (a′) Preflight corrections
None: no statement of (a) was found wrong. One observation, no change of any verdict: (a) names `stein_lwPoly` for the polynomial `X(α,y) X(y',w) P'`; stage 1b applied the same Stein identity (`stein_sample`) to the `C¹`-tame function `G_{αy} (G_{y'w} f)` (`lwG_tame1.mul`), so that polynomial is not formed.

## (b) Script output
Stage 1b: branch `t/T2120` at `c7fd80a` (base `d1cb5a6`); first `date -u` of stage 1b: Sun Oct  4 07:14:04 UTC 2026; last `date -u` (before the final builds above): Sun Oct  4 07:48:34 UTC 2026.
### Build, registry, axioms
```
$ lake build RBM3D.Graph.LWGGExp 2>&1 | tail -1 ;  lake env lean RBM3D/Graph/LWGGExp.lean 2>&1 | wc -l    # messages from the new file
Build completed successfully (3362 jobs).
0
$ lake build RBM3D.Test.Axioms 2>&1 | tail -1
Build completed successfully (2 jobs).
$ lake build   # whole library; `import RBM3D.Graph.LWGGExp` temporarily inserted after line 163 of RBM3D.lean (restored from a copy; `git status --short` empty afterwards); 07:45:48 -> 07:46:09 UTC
info: RBM3D.lean:167:0: axiom audit: 3716 theorems, 1301 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (3868 jobs).
$ grep -c "LWggExp" buildfull.log ; grep -n "LWedgeExp" buildfull.log      # registry ledger: LWggExp gone, LWedgeExp (LW-06) still owed
0
705:  RBM.Graph.LWedgeExp: 0 [no certificate]
777: RBM.Graph.LWedgeExp,
$ git diff --stat main...t/T2120 ; git diff main...t/T2120 -- RBM3D/Test/Axioms.lean | grep -E "^[-+][^-+]"
 RBM3D/Graph/LWGGExp.lean | 1748 ++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean   |    1 -
 2 files changed, 1748 insertions(+), 1 deletion(-)
-   `RBM.Graph.LWggExp, -- `(Oe2x)` (`7_8:334-349`): LW-07
$ grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Graph/LWGGExp.lean      # (Test/Axioms.lean has 1 match, its line 18, a docstring that is also on main)
0
$ #print axioms of the 57 public declarations of the file (names_new.txt = grep of ^theorem|def|abbrev), plus instT1, instT2 = the two target instances as defs
  50 = [propext, Classical.choice, Quot.sound]; 2 = "does not depend on any axioms" (oe2xRet, oe2xPhi);
  5 subsets: oe2xSplit [propext, Quot.sound]; oe2xInst_hq [propext, Quot.sound]; oe2xInstP, oe2xInstQ, oe2xInst_hy [propext];  sorryAx: 0
  lwGGExp_holds, oe2x_graph_E, oe2xR1_counters, oe2xR1_nM_ge, instT1, instT2 : [propext, Classical.choice, Quot.sound]
```
### Target statements, extracted from the file by script (`extract.py`: text from `theorem NAME` to `:=`; the counter and `ord` theorems: conclusion only, binders omitted)
```
theorem lwGGExp_holds (d : ℕ) : LWggExp d :=

theorem oe2x_graph_E (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) {m : ℂ}
    (hm0 : m ≠ 0) (hzm : z + (u : ℂ) * m = -m⁻¹)
    (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hSp : ∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j)
    (hM : ∀ a, M a a = m)
    (Γ : LGraph E I) (x : I) (y y' : E ⊕ I) (hy : y ≠ Sum.inr x)
    (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hp1 : p.1 = ⟨true, false, Sum.inr x, y⟩)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2)
    (hq1 : q.1 = ⟨true, false, y', Sum.inr x⟩)
    (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, Γ.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
      ∫ ω, (oe2xR1 m Γ p x y hy).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ∫ ω, (oe2xR2 m Γ q x y y').val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ∫ ω, (owxT1 m Γ x).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ∫ ω, (oe2xR4 m Γ q x y y').val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ∫ ω, (oe2xR5 m Γ q x y y').val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ∫ ω, (oe2xR6 m Γ q x y y').val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ((lwSplit q.2).map fun q' => ∫ ω, (oe2xR7 m Γ x y y' q').val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum +
      ((lwSplit q.2).map fun q' => ∫ ω, (oe2xR8 m Γ x y y' q').val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum :=

oe2xR1_counters :  (oe2xR1 m Γ p x y hy).nS + 1 = Γ.nS ∧ (oe2xR1 m Γ p x y hy).nW = Γ.nW ∧ (oe2xR1 m Γ p x y hy).nV + 1 = Γ.nV ∧ (oe2xR1 m Γ p x y hy).nM ≤ Γ.nM
oe2xR2_counters :  (oe2xR2 m Γ q x y y').nS + 1 = Γ.nS ∧ (oe2xR2 m Γ q x y y').nW = Γ.nW + 1 ∧ (oe2xR2 m Γ q x y y').nV = Γ.nV ∧ (oe2xR2 m Γ q x y y').nM ≤ Γ.nM
oe2xR4_counters :  (oe2xR4 m Γ q x y y').nS = Γ.nS + 1 ∧ (oe2xR4 m Γ q x y y').nW = Γ.nW + 2 ∧ (oe2xR4 m Γ q x y y').nV = Γ.nV + 2 ∧ (oe2xR4 m Γ q x y y').nM = Γ.nM
oe2xR5_counters :  (oe2xR5 m Γ q x y y').nS = Γ.nS + 1 ∧ (oe2xR5 m Γ q x y y').nW = Γ.nW + 1 ∧ (oe2xR5 m Γ q x y y').nV = Γ.nV + 1 ∧ (oe2xR5 m Γ q x y y').nM = Γ.nM
oe2xR6_counters :  (oe2xR6 m Γ q x y y').nS = Γ.nS + 1 ∧ (oe2xR6 m Γ q x y y').nW = Γ.nW + 2 ∧ (oe2xR6 m Γ q x y y').nV = Γ.nV + 2 ∧ (oe2xR6 m Γ q x y y').nM = Γ.nM
oe2xR7_counters :  (oe2xR7 m Γ x y y' q').nS = Γ.nS + 1 ∧ (oe2xR7 m Γ x y y' q').nW = Γ.nW + 1 ∧ (oe2xR7 m Γ x y y' q').nV = Γ.nV + 1 ∧ (oe2xR7 m Γ x y y' q').nM = Γ.nM
oe2xR8_counters :  (oe2xR8 m Γ x y y' q').nS = Γ.nS + 1 ∧ (oe2xR8 m Γ x y y' q').nW = Γ.nW + 2 ∧ (oe2xR8 m Γ x y y' q').nV = Γ.nV + 2 ∧ (oe2xR8 m Γ x y y' q').nM = Γ.nM
oe2xR1_nM_ge :  Γ.nM ≤ (oe2xR1 m Γ p x y hy).nM + 1
oe2xR2_nM_ge :  Γ.nM ≤ (oe2xR2 m Γ q x y y').nM + 1
oe2xR1_val :  (oe2xR1 m Γ p x y hy).val D ℓe = (oe2xR1d m Γ p x y).val D ℓe
oe2xR1_ord :  ord (oe2xR1 m Γ p x y hy).counters = ord Γ.counters + 1
oe2xR2_ord :  ord (oe2xR2 m Γ q x y y').counters = ord Γ.counters + 1
oe2xR4_ord :  ord (oe2xR4 m Γ q x y y').counters = ord Γ.counters + 1
oe2xR5_ord :  ord (oe2xR5 m Γ q x y y').counters = ord Γ.counters + 1
oe2xR6_ord :  ord (oe2xR6 m Γ q x y y').counters = ord Γ.counters + 1
oe2xR7_ord :  ord (oe2xR7 m Γ x y y' q').counters = ord Γ.counters + 1
oe2xR8_ord :  ord (oe2xR8 m Γ x y y' q').counters = ord Γ.counters + 1
```
(`R3` is the merged `owxT1`: `owxT1_counters`, `owxT1_ord` of `Graph/LWWeightExp`, `(1, 1, 1, 0)`, `ord + 1`.)
### Compiled nonempty instances (`grep -n "^example"` lines 1629 1633 1639 1671 1678 1705 1719; `d = 3`, `L = 3`, `W = 1`, `g = 1/2`, `E = 0`, `t = 1/2`, `N = (WL)^d = 27`; sources by script, first lines)
```
1629: example := lwGGExp_holds 3 3 1 (le_refl 3) (1 / 2) 0 (1 / 2) lwWx_inst_hE (by norm_num) (by norm_num)
  (0 : Idx 3 3 1) (Pi.single 0 1) (Pi.single 0 1) 1

/-- **Target 1 with a non-constant `f`** (`P = G_{xx}`, so that the derivative terms `R7`, `R8` are nonzero). -/
...
1633: example := lwGGExp_holds 3 3 1 (le_refl 3) (1 / 2) 0 (1 / 2) lwWx_inst_hE (by norm_num) (by norm_num)
  (0 : Idx 3 3 1) (Pi.single 0 1) 0 (MvPolynomial.X (true, (0 : Idx 3 3 1), 0))

/-- **Target 1, the instance of `Graph/LWPins.lean`** (`inst_gg`: `d = 3`, `L = 3`, `W = 2`, `N = 216`, `g = 1`,
...
1639: example (x y y' : Idx 3 3 2) := LWInstFixed.inst_gg (lwGGExp_holds 3) x y y'

/-- The graph `G_{xa} G_{bx} G_{aw} Ḡ_{wb}` with the waved edge `S_{xw}`: external vertices `a = inl 0`, `b = inl 1`,
internal vertices `x = inr 0`, `w = inr 1` (so `y = a`, `y' = b`, and `f = G_{aw} Ḡ_{wb}` has two solid edges). -/
...
1671: example := oe2x_graph_E (sz := lwWxInstSz) (n := 0) (gaussIBP lwWxInstSz) lwWx_inst_im
  (by norm_num : (0 : ℝ) < 1 / 2) (lwWx_mE_ne 0 lwWx_inst_hE) (lwWx_flow 0 (1 / 2) lwWx_inst_hE)
  lwWxInstSp lwWxInstM lwWx_inst_hSp lwWx_inst_hM (oe2xInstGraph (mE 0)) 0 (Sum.inl 0) (Sum.inl 1)
  oe2xInst_hy oe2xInstP (oe2xInst_hp _) rfl oe2xInstQ oe2xInst_hq rfl (fun _ => 0)

/-- **The counters of the eight terms at the instance**, by the counter theorems: `ord` rises by one in each term
...
1678: example :
    ord (oe2xR1 1 (oe2xInstGraph 1) oe2xInstP 0 (Sum.inl 0) oe2xInst_hy).counters =
      ord (oe2xInstGraph 1).counters + 1 ∧
    ord (oe2xR2 1 (oe2xInstGraph 1) oe2xInstQ 0 (Sum.inl 0) (Sum.inl 1)).counters =
      ord (oe2xInstGraph 1).counters + 1 ∧
    ord (owxT1 1 (oe2xInstGraph 1) 0).counters = ord (oe2xInstGraph 1).counters + 1 ∧
...
1705: example :
    (oe2xR1 1 (oe2xInstGraph 1) oe2xInstP 0 (Sum.inl 0) oe2xInst_hy).nM ≤ (oe2xInstGraph 1).nM ∧
    (oe2xInstGraph 1).nM ≤ (oe2xR1 1 (oe2xInstGraph 1) oe2xInstP 0 (Sum.inl 0) oe2xInst_hy).nM + 1 ∧
    (oe2xR2 1 (oe2xInstGraph 1) oe2xInstQ 0 (Sum.inl 0) (Sum.inl 1)).nM ≤ (oe2xInstGraph 1).nM ∧
    (oe2xInstGraph 1).nM ≤ (oe2xR2 1 (oe2xInstGraph 1) oe2xInstQ 0 (Sum.inl 0) (Sum.inl 1)).nM + 1 :=
  ⟨(oe2xR1_counters 1 _ oe2xInstP (oe2xInst_hp _) 0 _ oe2xInst_hy).2.2.2,
...
1719: example :
    let Γ := oe2xInstGraph 1
    (Γ.nS, Γ.nW, Γ.nV, Γ.nM) = (4, 1, 2, 1) ∧
    ((oe2xR1 1 Γ oe2xInstP 0 (Sum.inl 0) oe2xInst_hy).nS, (oe2xR1 1 Γ oe2xInstP 0 (Sum.inl 0) oe2xInst_hy).nW,
      (oe2xR1 1 Γ oe2xInstP 0 (Sum.inl 0) oe2xInst_hy).nV, (oe2xR1 1 Γ oe2xInstP 0 (Sum.inl 0) oe2xInst_hy).nM) =
      (3, 1, 1, 0) ∧
...
```
Types of the first and of the graph instance (`#print instT1`, `#print instT2` with `pp.proofs false`; the right sides continue with the eight terms):
```
def instT1 : ∫ (ω : Ω 3 3 1),
    LWPins_lwG 3 3 1 0 (1 / 2) ω 0 (Pi.single 0 1) * LWPins_lwG 3 3 1 0 (1 / 2) ω (Pi.single 0 1) 0 *
      LWPins_lwf 3 3 1 0 (1 / 2) 1 ω ∂PF 3 3 1 (1 / 2) =
  ∫ (ω : Ω 3 3 1),
    (mE 0 * if 0 = Pi.single 0 1 then 1 else 0) * LWPins_lwG 3 3 1 0 (1 / 2) ω (Pi.single 0 1) 0 *
                    LWPins_lwf 3 3 1 0 (1 / 2) 1 ω +
                  mE 0 ^ 3 * LWPins_lwSp 3 3 1 (1 / 2) 0 (1 / 2) 0 (Pi.single 0 1) *
...
def instT2 : ∫ (ω : lwWxInstSz.SeqΩ),
    (oe2xInstGraph (mE 0)).val
      (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp ω) fun x =>
      0 ∂lwWxInstSz.seqP =
  ∫ (ω : lwWxInstSz.SeqΩ),
                  (oe2xR1 (mE 0) (oe2xInstGraph (mE 0)) oe2xInstP 0 (Sum.inl 0) oe2xInst_hy).val
```
Counters at the graph instance (`decide`, line 1719; `Γ = G_{xa} G_{bx} G_{aw} Ḡ_{wb}` with `S_{xw}`, `x = inr 0`, `y = a`, `y' = b`): `(n_S, n_W, n_V, n_M)`: `Γ (4,1,2,1)` `ord 2`; `R1 (3,1,1,0)`, `R2 (3,2,2,0)`, `R3 (5,2,3,1)`, `R4 (5,3,4,1)`, `R5 (5,2,3,1)`, `R6 (5,3,4,1)`, `R7` two graphs `(5,2,3,1)`, `R8` two graphs `(5,3,4,1)`; `ord 3` each (the same counters by the counter theorems: example at line 1678).
### Name-clash grep, ports
```
$ for NAME in the 57 public names of the file: git grep -nE "(theorem|def|abbrev|lemma|structure|instance)[[:space:]]+([A-Za-z_.]*\.)?NAME([[:space:]]|$|\()" main -- 'RBM3D/*.lean'
public names checked: 57; clash candidates on main (c24f54b): 0
$ git log --oneline d1cb5a6..main ; git diff --name-only d1cb5a6 main | grep -v "^docs/"     # main since the branch base
c24f54b T2117: merge S1-26 Green/MinorDiffCond
RBM3D.lean
RBM3D/Green/MinorDiffCond.lean
```
No port from RBM1D/RBM2D: nothing was copied, no `git diff --stat` for ports.

### Narrative (≤ 40 lines)
1. Verdict: both targets delivered in `RBM3D/Graph/LWGGExp.lean` (1748 lines, 57 public declarations, 7 `example`s) and the registry line; no hypothesis added, no pin or merged file touched (`LWPins.lean`, `LWWeightExp.lean` unchanged: the diff above lists two files).
2. Target 1, `lwGGExp_holds : ∀ d, LWggExp d` (pin as fixed by §34, every `d`, `g`, `3 ≤ L`, `W ≥ 1`, `|E| < 2`, `0 ≤ t < 1`; the pin is true as written). Pathwise: `oe2x_defect_identity` (`G_{xy} G_{y'x} f` minus the eight terms `= -m Σ_w (δ_{xw} + m² S⁺_{xw}) Z_w`, `Z_w = oe2xDefect`, twin of `owx_defect_identity`; the resummation uses `S⁺ - m² S⁺ S = S`).
3. `E Z_w = 0`: `oe2x_resolvent_id` (off-diagonal `Σ_α H_{wα} G_{αy} = δ_{wy} + z G_{wy}`), Leibniz (`lwStein_dh_mul`) and `dhSample_lwG` for `∂_{αw}(G_{αy} G_{y'w} f)`, `stein_sample` for each `α` (`integral_oe2xDefect`); then `oe2x_integral` (the pin on `Sizes.seqP`, `hG := gaussIBP sz`). `0 < t < 1`: the bridge of T2107 (`lwWx_integral`, `lwWx_lwPoly`, `lwWx_lwdf`, `lwWx_hSp`, `lwWx_flow`, `lwWx_im_pos`). `t = 0`: `oe2x_lwG_zero` (`G = m I`), both sides are `m² δ_{xy} δ_{y'x} f`.
4. Registry: the owed line `RBM.Graph.LWggExp` removed from `RBM3D/Test/Axioms.lean`; the full-build ledger above no longer lists it.
5. Target 2, the eight terms as graphs on `I`, `I ⊕ Fin 1`, `I ⊕ Fin 2` (the `owxT*` pattern, `LGraph.owxExt`): `R1 = oe2xR1` (`x` merged into `y`, a graph on `{i // i ≠ x}`, vertex map `oe2xPhi`), `R2 = oe2xR2`, `R3 = owxT1` (reused), `oe2xR4`, `oe2xR5`, `oe2xR6`, and one graph for each solid edge of `f` in `oe2xR7 q'`, `oe2xR8 q'` (`q' ∈ lwSplit q.2`, derivative edges `owxDE`, sign in `owxDE` as in `owxT3`, `owxT4`).
6. Form for LW-08: `Γ` with `p ∈ lwSplit Γ.solid`, `p.1 = G_{xy}` (blue, no circle, `x` internal), `q ∈ lwSplit p.2`, `q.1 = G_{y'x}`, `q.2 = f`; `y ≠ x` as vertices (`hy`), `y'` arbitrary; then `oe2x_graph_E`: `E Γ.val = E R1.val + E R2.val + E R3.val + E R4.val + E R5.val + E R6.val + Σ_{q'} E R7_{q'}.val + Σ_{q'} E R8_{q'}.val` (data `M_{aa} = m`, `S = lwS`, `S⁺ (1 - m² S) = S`, `0 < u`, `z + u m = -m⁻¹`, `Im z > 0`). One labelling: `oe2x_term_integral`; `R1` through `oe2xR1d` (the same graph with the `=`-dotted edge `x = y`, all `y`) and `oe2xR1_val` (reindexing `oe2xSplit`).
7. Counters (all with `nS`, `nW`, `nV` exact): `R3, R5, R7: (+1,+1,+1)`, `R4, R6, R8: (+1,+2,+2)`, `R2: (-1,+1,0)`, `R1: (-1,0,-1)`; `n_M` unchanged in `R3`-`R8`; in `R1`, `R2` between `n_M(Γ) - 1` and `n_M(Γ)` (`oe2x_nM_le`, `oe2x_nM_add_edge`; the value `-1` occurs at the instance); `ord = ord Γ + 1` for each of the eight.
8. Stop conditions: none. No definition outside `LWVocab`/`LWStein`/`LWWeightExp` was needed for the counters (`nM` through `LGraph.nM_eq_card`, `molGraph`).
9. Reuse: no merged declaration is restated or redefined; merged declarations are used as they are (`owxExt`, `owxEmb`, `owxLab1/2`, `owxDE`, `owxT1`, `owx_integral_val1/2`, `owxExt_nM`, `owxExt_reach1/2`, `lwWx_*`, `lwStein_*`, `stein_sample`, `lwG_tame1`, `LGraph.relabel`). The proof texts of `oe2x_defect_identity`, `oe2x_resolvent_id`, `integral_oe2xDefect`, `oe2x_integral`, `oe2x_term_integral`, `oe2x_graph_E`, `oe2x_adj_owxExt` and the local macro `oe2x_tame` are adapted from the merged `owx_defect_identity`, `lwStein_resolvent_id`, `integral_owxDefect`, `owx_integral`, `owx_term_integral`, `owx_graph_E`, `owxExt_nM` and `lwx_tame` (new statements, same pattern).

## (c) Mathlib names verified (`#check` in `mlnames.lean`: 18 exist) and absent
`Finite.card_option`, `Nat.card_le_card_of_injective`, `Fintype.card_subtype_compl`, `Fintype.card_subtype_eq`, `Fintype.card_pos_iff`, `SimpleGraph.Reachable.mono`, `SimpleGraph.ConnectedComponent.{lift,ind,eq}`, `SimpleGraph.Adj.reachable`, `SimpleGraph.Walk.reverse`, `Function.surjInv_eq`, `Equiv.sum_comp`, `Fintype.sum_prod_type`, `Finset.sum_ite_eq'`, `MeasureTheory.integral_finsetSum`, `MeasureTheory.integral_congr_ae`, `List.map_congr_left`.
Absent: `Nat.card_option` (`error(lean.unknownIdentifier)`); use `Finite.card_option`.

## (d) Open issues and paper-delta candidates
- **T2120a**: the expansion-term table of `docs/reports/T2040-prove.md` (lines 57, 59: `Oe2x-R1`, `Oe2x-R2`) lists `(dS,dW,dV,dM) = (-1,0,-1,0)` and `(-1,1,0,0)`, i.e. `ΔnM = 0` for `R1`, `R2`; the Lean statements give `n_M(Γ) - 1 ≤ n_M(R) ≤ n_M(Γ)` (the merge `x ↦ y` and the new waved edge `S⁺_{xy}` can join two molecules), and `n_M(R) = n_M(Γ) - 1` occurs (instance above, `(1) -> (0)`). `ord` does not involve `n_M`; the other six terms keep `n_M`.
- **T2120b**: `R1` (`m δ_{xy} G_{y'x} f`) has `Δ(n_S, n_W, n_V) = (-1, 0, -1)` only when `x` is merged into a different vertex; `oe2x_graph_E` therefore assumes `y ≠ x` as vertices (`hy`). For `y = x` the factor `G_{xx}` is a weight and the term is the unmerged graph without that edge (`Δord = -1`, see the last line of the counters script in (a)): not stated here; the value identity `oe2x_term_integral` (with `oe2xR1d`) holds for every `y`.
- **T2120c**: the paper's `=_E` of `(Oe2x)` is read as equality of the expectations (the pin `LWggExp`), for every resolvent polynomial `f` (T2040d) and the flow data `S = t svarF`, `z + t m = -m⁻¹`, `S⁺ = S (1 - m² S)⁻¹` with the argument order `(g, E, t)` of §34; `∂_{h_{αx}}` is `dhSample` (T2060a).
- **T2120d**: as a graph operation `f` is the product of the solid edges other than `G_{xy}`, `G_{y'x}` (`q.2`), each of them (weights and light-weights included) differentiated in one graph of `R7`, `R8`; `G_{xy}`, `G_{y'x}` are blue and without circle; `y' = x` is allowed (the edge `G_{xx}`).
- Observation: the branch base is `d1cb5a6`; main has one later merge (`c24f54b`, `Green/MinorDiffCond`: a new file and a root import); the hub's full build at merge is the check on the merged tree.
- All targets delivered: `all_targets_done = true`.

