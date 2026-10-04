Prover model: claude-sonnet-5-5
## (a) Math preflight — Sun Oct  4 07:16:23 UTC 2026
Scripts (python3+numpy, outside the repo, no Lean): `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2119` (`mc_oe1x.py` reuses `T2107/model.py`: `svarF`, `sampleX`, `H_t = √t X`, `S = t·svarF`).
Notation: `m = mE E`, `z = zt E t`, `Ǧ = G - m`, `𝒢 = G_{xy₀}·R·f`, `R = LWPins_oe1xRest` (pin `k₁` = paper `k₁-1`, so `y₀ = y 0` = paper `y₁`). Pin: `Graph/LWPins.lean:131-160`, no `S⁺`; real-argument order checked against `variable (g E t : ℝ)` (`:77`, §34 lesson): `lwG/lwGb/lwGc/lwGcb d L W E t`, `lwS d L W g t`, `lwf/lwdf/oe1xRest d L W E t`, `PF d L W g`: all calls in the pin match.

### (i) Exponent table (the pin has no exponents; thresholds, identities, counters)
| item | value | constraint | slack |
|---|---|---|---|
| `|E| < 2` | `Im m = √(4-E²)/2`, `‖m‖ = 1` | `Im z = (1-t) Im m > 0` for `t<1` (`lwWx_im_pos`); `m ≠ 0` (`lwWx_mE_ne`) | `Im z = 0.500` at the instance, `0.087` at `E=1,t=0.9` (det.py below); `→ 0` only at `t→1` or `E=±2`, both outside the pin |
| `0 ≤ t < 1` | pin | `t>0` for `stein_*`, `dhSample_lwG` (need `0<u`; `dhSample` has `0⁻¹=0`); `t=0` separate | none needed |
| flow relation | `z + t m = -m⁻¹` (`lwWx_flow`) | resolvent identity `G_{xy} = mδ_{xy} - m(HG)_{xy} - t m² G_{xy}` (from `(H-z)G=I`, `z=-m⁻¹-tm`) | pathwise residual `≤ 1.4e-15` (det.py) |
| row sums of `S` | `Σ_α S_{xα} = t` (`lwS_row_sum`, `LWStein.lean:1215`; `lwWx_lwS`: `lwS sz 0 t = of LWPins_lwS`) | cancels `t m²𝒢` against `m²(ΣS)𝒢`, see "no `S⁺`" | `|rowsum - t| ≤ 1.1e-16` for `d=3`, `g=½`, `W∈{1,2}` |
| `g` | enters `svarF` only through `g²`; pin has `∀ g : ℝ` | none | `g ≤ 0` covered (T2107 (a): `S(g)=S(-g)`) |
| `L, W, d` | `3 ≤ L` (pin), `NeZero W`, `∀ d` | `lwS_row_sum` uses `card_nbhd` only; no `L–W` relation, no `ℓ`, no `∀ᶠ n` (§29 items (2)(3)(4) not triggered) | none |
| `k₁…k₄ ≥ 0` | `y : Fin (k₁+1) → Idx`, empty products for `k₂=k₃=k₄=0` | `Finset.univ.erase i` for `i : Fin k₂`, `Fin k₃`; coefficients `(k₁:ℂ)`, `(k₄:ℂ)` vanish at `0` | cases `(0,0,0,0)`, `(1,1,0,0)`, `(0,1,1,0)`, `(0,1,1,1)` all run (below) |
| Stein step | `∫ H_{xα}F = S_{xα}∫ ∂_{h_{αx}}F` = `stein_sample` (`w := x`, `hG := gaussIBP sz`, merged, not a hypothesis) with `F = G_{αy₀}·R·f` a `lwPoly` (via `lwWxRename`, swap `(false,a,b)↦(b,a,false)`, T2107) | `Tame1`; `lwStein_dh_mul` (Leibniz) | no external hypothesis, so no limit computation |
| derivative rules (`∂=∂_{h_{αx}}`, `∂_{αw}G_{ab}=-G_{aα}G_{wb}`, `∂_{αw}Ḡ_{ab}=-Ḡ_{aw}Ḡ_{αb}`; `dhSample_lwG`, `_star`) | `G_{αy₀}`: `-G_{αα}G_{xy₀}`; `G_{xy_i}` (`i≥1`): `-G_{xα}G_{xy_i}`; `Ḡ_{xy'_i}`: `-Ḡ_{xx}Ḡ_{αy'_i}`; `G_{w_ix}`: `-G_{w_iα}G_{xx}`; `Ḡ_{w'_ix}`: `-Ḡ_{w'_ix}Ḡ_{αx}` | each sign checked by the nine-term MC below | see MC |
| nine terms from `𝒢 = mδR f - m Σ_α H_{xα}G_{αy₀}Rf - tm²𝒢` | T1 `mδ_{xy₀}Rf`; from `∂G_{αy₀}`: `mΣS G_{αα}𝒢 = mΣS Ǧ_{αα}𝒢 + m² t𝒢` (T2 + the cancelling `tm²𝒢`); from `Ḡ_{xy'_i}`: `mḠ_{xx}ΣS G_{αy₀}Ḡ_{αy'_i}` with `Ḡ_{xx}=Ǧ̄_{xx}+m̄` (T3 `|m|²`, T5 `mǦ̄_{xx}`); from `G_{w_ix}`: `mG_{xx}…` (T4 `m²`, T6 `mǦ_{xx}`); from `G_{xy_i}`, `i≥1` (`k₁` of them): T7 `k₁ m ΣS G_{xα}G_{αy₀}`; from `Ḡ_{w'_ix}`: T8 `k₄ m ΣS Ḡ_{αx}G_{αy₀}`; from `f`: T9 `-mΣS R G_{αy₀}∂_{h_{αx}}f` | matches pin terms 1-9 (`LWPins.lean:136-158`) one by one | MC |
| why no `S⁺` here | `m²ΣS_{xα}𝒢 = tm²𝒢` cancels the `-tm²𝒢` of the resolvent identity exactly (row sum `= t`, flow relation). In `(Owx)` the LHS is `Ǧ_{xx}f = G_{xx}f - mf`; the same step leaves `m²ΣS_{xα}Ǧ_{αα}f`, which `(Owx)` at `α` iterates to `S⁺ = S(1-m²S)⁻¹` (needs `lwS_isUnit`, `‖m‖²t<1`) | `S⁺` not used in `LWedgeExp`: no `hSp`, no `lwSplus` | `1-‖m‖²t = 1-t > 0` only matters for `(Owx)` |
| case `t = 0` | `H_0 = 0`, `S = 0`, `G = (−z)⁻¹I = mI` (`z=-m⁻¹`; `lwWx_gc_zero`, `lwWx_lwS_zero`) | LHS `= mδ_{xy₀}·Rf` (`G_{xy₀} = mδ`); RHS `= T1` since T2…T9 each carry `Σ_α S_{xα} = 0` (T9: `0·∂f`, no differentiability) | exact: MC script prints `max|LHS-RHS| = 0` (`2.2e-16` at `E=1`) |
| counters, `x` internal, `e₀ = G_{xy₀}`, `y₀ ≠ x` | `(ΔnS,ΔnW,ΔnV,ΔnM; Δord = ΔnS+2(ΔnW-ΔnV))`: T1 `(-1,0,-1,0 or -1; +1)`; T2 `(1,1,1,0;+1)`; T3, T4 `(0,1,1,0; 0)`; T5, T6 `(1,1,1,0;+1)`; T7, T8 `(1,1,1,0;+1)`; T9 (one graph per solid edge of `f`) `(1,1,1,0;+1)` | T1: dotted `=`-edge `x–y₀` and `e₀` removed, read through `LGraph.merge` (`LWVocab:778`) or `relabel` onto `I' = {i // i ≠ x}`; T2 is `owxT1 m Γ x` verbatim; T3-T9: `owxExt`/`owxDE` (`owxDE α x`) with a leaf `α` on `x`, `nM` by `owxExt_nM`/`owx_nM_eq` | script below; slack: `Δord ≥ 0` for all nine, `= 0` only for T3, T4 (structural, matches T2040 (a)(i)) |
| T2040 table correction | T1 `ΔnM`: merging `x` with `y₀` in another internal molecule or an external one gives `ΔnM = -1` (script, `y₁=a`), `0` if same molecule | size `(L^d)^{nM}` only decreases (`L^d>1`); `ord` has no `nM` | paper-delta candidate `T2119a` (T2040's row `Oe1x-delta` lists `dM = 0`) |
| `y₀ = x` (`e₀` a weight) | T1 `= (-1,0,0,0; -1)`: no vertex lost | graph-level T1 counter needs `y₀ ≠ x`; the value-level pin `LWedgeExp` has no such restriction (`if x = y 0`) | stage 1b: hypothesis `e₀.dst ≠ e₀.src` on the counter theorem; the identity holds for both |
| definitions outside `LWVocab` | none needed: `LGraph`, `SEdge`, `WEdge`, `DEdge`, `merge`, `relabel`, `owxExt`, `owxDE`, `owxT1` exist; new items are lemmas (`nV` of the merge, `ΔnM ≤ 0` for T1) | | not BLOCKED |

### (ii) One concrete nondegenerate instance
`cd $S && python3 inst.py` (verbatim; Lean instance `d=3, L=3, W=1, g=½, E=0, t=½, (k₁,k₂,k₃,k₄)=(0,1,1,0), P=1`; terms T1…T6 present, T7, T8 have coefficient 0, T9 `=0` since `∂1 = 0`; MC columns from `mc_oe1x.py` below):
```
hyps: |E|<2 True; 0<=t<1 True; 3<=L True; W>=1 True; N=(WL)^d=27; k=(0, 1, 1, 0) (blue out-edges k1+1=1, red out 1, blue in 1, red in 0); P=1
m=1j |m|=1.000 Im z=0.500  row sum of S=t*S^B: 0.500000000000 (t=0.50)  |S|_max=0.2000
diag f=1 (P=1): LHS -0.0022+1.4339j T1..T9 (T7,T8,T9 vanish: k1=k4=0, df=0): +0.0000+1.2976j +0.0017-0.0062j -0.0004+0.3151j +0.0003-0.2702j +0.0004+0.1033j +0.0008+0.0006j +0.0000+0.0000j +0.0000+0.0000j +0.0000+0.0000j | LHS-RHS -0.0050-0.0063j SE 0.0109
off f=1 (P=1): LHS +0.0003+0.0931j T1..T9 (T7,T8,T9 vanish: k1=k4=0, df=0): +0.0000+0.0000j +0.0001+0.0003j +0.0001+0.0918j -0.0000-0.0226j -0.0001+0.0251j -0.0000+0.0007j +0.0000+0.0000j +0.0000+0.0000j +0.0000+0.0000j | LHS-RHS +0.0003-0.0022j SE 0.0013
```
(`diag`: all vertices `= x = 0`; `off`: `y₀ = (1,0,0)`, `y'₀ = (1,0,0)`, `w₀ = x`; 10⁴ samples.) Deterministic checks, `python3 det.py` (verbatim):
```
W=1 E=0 t=0.5: |z+t m + 1/m|=0.0e+00  rowsum(S)-t: max 1.1e-16  pathwise |G-(mI-mHG-t m^2 G)|=4.4e-16  Im z=0.500 |m|=1.000
W=1 E=1 t=0.9: |z+t m + 1/m|=2.0e-16  rowsum(S)-t: max 1.1e-16  pathwise |G-(mI-mHG-t m^2 G)|=9.2e-16  Im z=0.087 |m|=1.000
W=2 E=1 t=0.5: |z+t m + 1/m|=1.6e-16  rowsum(S)-t: max 0.0e+00  pathwise |G-(mI-mHG-t m^2 G)|=1.4e-15  Im z=0.433 |m|=1.000
```
Target 2 data: base graph `x, u` internal (waved `x–u`), `a,b,c,e` external; solid `G_{xy₁}`, `G_{xu}`, `Ḡ_{xb}`, `G_{cx}`, `Ḡ_{ex}`, `f`-edge `Ḡ_{ua}`. `python3 counters.py` (verbatim; `delta = (ΔnS,ΔnW,ΔnV,ΔnM,Δord)`):
```
y1=a base (nS,nW,nV,nM,ord)=(6, 1, 2, 1, 4)
  T1 m delta_{x y1} (merge)  delta=(-1, 0, -1, -1, 1)
  T2 m S Gc_aa (G kept)      delta=(1, 1, 1, 0, 1)
  T3 |m|^2 pull(G_al y1,Gb_al yp) delta=(0, 1, 1, 0, 0)
  T4 m^2 pull(G_al y1,G_w al) delta=(0, 1, 1, 0, 0)
  T5 m Gcb_xx pull (red)     delta=(1, 1, 1, 0, 1)
  T6 m Gc_xx pull (blue in)  delta=(1, 1, 1, 0, 1)
  T7 k1 m G_x al G_al y1     delta=(1, 1, 1, 0, 1)
  T8 k4 m Gb_al x G_al y1    delta=(1, 1, 1, 0, 1)
  T9 -m deriv of f-edge      delta=(1, 1, 1, 0, 1)
y1=u base (nS,nW,nV,nM,ord)=(6, 1, 2, 1, 4)
  T1 m delta_{x y1} (merge)  delta=(-1, 0, -1, 0, 1)
  (T2..T9 identical to y1=a)
y1=x (e0 weight) T1 delta=(-1, 0, 0, 0, -1)
```
Monte Carlo of `(Oe1x)`: `d=3, L=3, g=½`, `x=0`, 10⁴ samples of `H_t`; `(k₁,k₂,k₃,k₄) ∈ {(0,0,0,0),(1,1,0,0),(0,1,1,1),(0,1,1,0)}`, two vertex choices (`diag`, `off`), `f ∈ {1, G_{xx}}` (`∂_{h_{αx}}G_{xx} = -G_{xα}G_{xx}`): 16 rows per `(W,E,t)`; the nine terms are summed separately inside the script (`T[1..9]`) and the instance row above prints them. `|LHS-RHS|/SE` is the mean over 10⁴ samples of the pin's difference divided by its standard error; "power" row: the same statistic after deleting `T_j` (max over the 16 rows), to show that each term is detected. `cd $S && python3 mc_oe1x.py 1 0,1 0,0.5,0.9; python3 mc_oe1x.py 2 0,1 0,0.5,0.9` (verbatim):
```
W=1 E=0 t=0: 16 rows (4 k x 2 vertex sets x 2 f): max|term|=1.0e+00 max|LHS-RHS|=0.0e+00
W=1 E=0 t=0.5: 16 rows, max |LHS-RHS|/SE = 1.89, mean = 1.14
   power: max_rows |LHS-RHS+T_j|/SE for j=1..9 (dropping T_j): 162 6 73 27 26 5 24 36 20
W=1 E=0 t=0.9: 16 rows, max |LHS-RHS|/SE = 1.90, mean = 1.15
   power: max_rows |LHS-RHS+T_j|/SE for j=1..9 (dropping T_j): 54 8 16 9 19 8 13 14 6
W=1 E=1 t=0: 16 rows (4 k x 2 vertex sets x 2 f): max|term|=1.0e+00 max|LHS-RHS|=2.2e-16
W=1 E=1 t=0.5: 16 rows, max |LHS-RHS|/SE = 1.17, mean = 0.80
   power: max_rows |LHS-RHS+T_j|/SE for j=1..9 (dropping T_j): 159 7 62 21 21 9 22 30 16
W=1 E=1 t=0.9: 16 rows, max |LHS-RHS|/SE = 0.86, mean = 0.41
   power: max_rows |LHS-RHS+T_j|/SE for j=1..9 (dropping T_j): 47 5 10 6 15 6 9 9 3
W=2 E=0 t=0: 16 rows (4 k x 2 vertex sets x 2 f): max|term|=1.0e+00 max|LHS-RHS|=0.0e+00
W=2 E=0 t=0.5: 16 rows, max |LHS-RHS|/SE = 1.83, mean = 0.88
   power: max_rows |LHS-RHS+T_j|/SE for j=1..9 (dropping T_j): 523 2 96 10 5 2 10 18 9
W=2 E=0 t=0.9: 16 rows, max |LHS-RHS|/SE = 1.14, mean = 0.83
   power: max_rows |LHS-RHS+T_j|/SE for j=1..9 (dropping T_j): 264 3 80 9 16 3 9 23 7
W=2 E=1 t=0: 16 rows (4 k x 2 vertex sets x 2 f): max|term|=1.0e+00 max|LHS-RHS|=2.2e-16
W=2 E=1 t=0.5: 16 rows, max |LHS-RHS|/SE = 1.29, mean = 1.02
   power: max_rows |LHS-RHS+T_j|/SE for j=1..9 (dropping T_j): 523 1 98 11 7 2 12 17 11
W=2 E=1 t=0.9: 16 rows, max |LHS-RHS|/SE = 1.03, mean = 0.49
   power: max_rows |LHS-RHS+T_j|/SE for j=1..9 (dropping T_j): 266 3 75 8 14 2 9 23 7
```
Limits of the MC: at `W=2` the terms with a centred weight (T2, T6) are detected only at `1-3 SE` (`Ǧ` is small there); at `W=1` every term is detected at `≥ 3 SE` (T9 at `E=1, t=0.9`) and `≥ 5 SE` otherwise. The two-term cancellation `m²t𝒢` is tested by the identity, not by MC (det.py residual).

### Verdicts
- **Target 1 `lwEdgeExp_holds : LWedgeExp d`: PASS.** All hypotheses hold at the instance and on the grid (`W∈{1,2}`, `E∈{0,1}`, `t∈{0,½,0.9}`, 4 `k`-tuples, 2 vertex sets, 2 `f`); the nine terms follow from the Stein identity with the derivative rules above, the pin has no `S⁺`; `t=0` is the exact case `G=mI`, `S=0`. Stage 1b needs: the polynomial `P' = X(true,α,y₀)·R-monomial·rename P` for `F` (red variables with the swap `(false,a,b)↦(b,a,false)`, T2107), the `∂` of the product by `lwStein_dh_mul` repeated over the finite products of `R`, `Σ_α S_{xα}=t`.
- **Target 2 `(Oe1x)` as graph operation: PASS with notes.** Counters and `ord` per term as in the table (`Δord ≥ 0`; `0` only for T3, T4); T2 is the merged `owxT1`. Notes: (1) T1 needs `y₀ ≠ x` for `Δord = +1` and its `ΔnM ∈ {0,-1}` (candidate `T2119a`: T2040's table says `dM=0`); (2) the `k₁`, `k₄` terms are single graphs with coefficient `k₁ m`, `k₄ m` (the pin has one summand each), the `k₂`, `k₃` sums and T9 one graph per edge; (3) no definition outside `LWVocab` is needed, only new lemmas (`nV`/`nM` of the T1 merge). No hypothesis set empty or collapsed.

## (b) Script output — Sun Oct  4 07:50:51 UTC 2026
### Build, registry, axioms (branch t/T2119 at 3b7fd46; base f4cc46d)
```
$ lake build RBM3D.Graph.LWEdgeExp 2>&1 | tail -1;  … | grep -c "LWEdgeExp.lean:"   # messages of the new file
Build completed successfully (3362 jobs).
0
$ lake build RBM3D.Test.Axioms 2>&1 | tail -1
Build completed successfully (2 jobs).
$ lake build   # whole library; `import RBM3D.Graph.LWEdgeExp` temporarily inserted after line 162 of RBM3D.lean (restored; `git status --short` empty afterwards); run of Sun Oct  4 07:48:50 UTC 2026, log buildfull2.log
info: RBM3D.lean:166:0: axiom audit: 3685 theorems, 1302 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (3867 jobs).
$ grep -c "LWedgeExp" buildfull2.log ; grep -n "LWggExp" buildfull2.log   # registry ledger: LWedgeExp gone, LWggExp still owed
0
705:  RBM.Graph.LWggExp: 0 [no certificate]
777: RBM.Graph.LWggExp,
$ #print axioms of the public declarations of the file (grep of ^theorem|def|abbrev|lemma; names.txt):
  public declarations:       61; [propext, Classical.choice, Quot.sound]: 51; subsets of the three (the instance data/membership proofs): 8; no axioms: 2; sorryAx: 0
oe1x_integral : [propext, Classical.choice, Quot.sound]
lwEdgeExp_holds : [propext, Classical.choice, Quot.sound]
oe1x_graph_Ed : [propext, Classical.choice, Quot.sound]
oe1xT1_counters : [propext, Classical.choice, Quot.sound]
oe1xDs_counters : [propext, Classical.choice, Quot.sound]
oe1xDs_ord : [propext, Classical.choice, Quot.sound]
oe1x_graph_E : [propext, Classical.choice, Quot.sound]
oe1x_graph_E_loop : [propext, Classical.choice, Quot.sound]
$ grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Graph/LWEdgeExp.lean
0
$ git diff --stat main...t/T2119
 RBM3D/Graph/LWEdgeExp.lean | 1545 ++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean     |    1 -
 2 files changed, 1545 insertions(+), 1 deletion(-)
$ git diff -U0 main...t/T2119 -- RBM3D/Test/Axioms.lean | grep -E "^[-+][^-+]"   # registry: the owed line of the proved pin
-   `RBM.Graph.LWedgeExp, -- `(Oe1x)` (`7_8:309-330`): LW-06
```
### Target statements, extracted from the file by script (`python3 extract.py NAME…`, statement up to `:=`; the pin `LWedgeExp` itself is unchanged: `git diff main...t/T2119 -- RBM3D/Graph/LWPins.lean | wc -l` =        0)
```
theorem lwEdgeExp_holds (d : ℕ) : LWedgeExp d :=
theorem oe1x_integral (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) {m : ℂ}
    (hm0 : m ≠ 0) (hzm : z + (u : ℂ) * m = -m⁻¹)
    {f : Sizes.SeqΩ sz → ℂ} (hf : Tame1 sz n f)
    (x y : Idx d (sz.L n) (sz.W n)) :
    ∫ ω, lwG sz n z u x y ω * f ω ∂(Sizes.seqP sz) =
      ∫ ω, (m * (if x = y then 1 else 0) * f ω +
          m * (∑ α, lwS sz n u x α * (lwG sz n z u α α ω - m)) *
            (lwG sz n z u x y ω * f ω) -
          m * ∑ α, lwS sz n u x α * lwG sz n z u α y ω * dhSample sz n u α x f ω)
        ∂(Sizes.seqP sz) :=
theorem oe1x_graph_E (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) {m : ℂ}
    (hm0 : m ≠ 0) (hzm : z + (u : ℂ) * m = -m⁻¹)
    (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hM : ∀ a, M a a = m)
    (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : I)
    (v : E ⊕ I) (hx : p.1 = ⟨true, false, Sum.inr x, v⟩) (hv : v ≠ Sum.inr x)
    (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, Γ.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
      ∫ ω, (oe1xT1 m Γ p x v hv).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ∫ ω, (owxT1 m Γ x).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ((lwSplit p.2).map fun q => ((oe1xDs m Γ x v q).map fun T => ∫ ω, T.val
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum).sum :=
theorem oe1xT1_counters (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (x : I) (v : E ⊕ I) (hv : v ≠ Sum.inr x) :
    (oe1xT1 m Γ p x v hv).nS + 1 = Γ.nS ∧ (oe1xT1 m Γ p x v hv).nW = Γ.nW ∧
      (oe1xT1 m Γ p x v hv).nV + 1 = Γ.nV ∧ (oe1xT1 m Γ p x v hv).nM ≤ Γ.nM :=
theorem oe1xT1_ord (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (x : I) (v : E ⊕ I) (hv : v ≠ Sum.inr x) :
    ord (oe1xT1 m Γ p x v hv).counters = ord Γ.counters + 1 :=
theorem oe1xDs_counters (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (x : I) (v : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hq : q ∈ lwSplit p.2) :
    ∀ T ∈ oe1xDs m Γ x v q, T.nW = Γ.nW + 1 ∧ T.nV = Γ.nV + 1 ∧ T.nM = Γ.nM ∧
      (T.nS = Γ.nS + 1 ∨ (T.nS = Γ.nS ∧ ((q.1.σ = false ∧ q.1.src = Sum.inr x) ∨
        (q.1.σ = true ∧ q.1.dst = Sum.inr x)))) :=
theorem oe1xDs_ord (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (x : I) (v : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hq : q ∈ lwSplit p.2) :
    ∀ T ∈ oe1xDs m Γ x v q, ord T.counters = ord Γ.counters + 1 ∨
      (ord T.counters = ord Γ.counters ∧ ((q.1.σ = false ∧ q.1.src = Sum.inr x) ∨
        (q.1.σ = true ∧ q.1.dst = Sum.inr x))) :=
```
(also in the file, same shape: `oe1x_graph_Ed` (dotted form of term 1, any `v`), `oe1x_graph_E_loop` (`y₁ = x`: `oe1xT1loop`), `oe1xT1loop_counters`, `oe1xD_counters`, `oe1xP_counters`, `oe1xD_ord`.)
### Compiled nonempty instances (`grep -n "^example"`, first line of each; `d = 3`, `L = 3`, `W = 1`, `g = 1/2`, `E = 0`, `t = 1/2`, `N = (WL)^d = 27` unless said)
```
1376:example := lwEdgeExp_holds 3 3 1 (le_refl 3) (1 / 2) 0 (1 / 2) lwWx_inst_hE (by norm_num) (by norm_num)
1381:example := lwEdgeExp_holds 3 3 1 (le_refl 3) (1 / 2) 0 (1 / 2) lwWx_inst_hE (by norm_num) (by norm_num)
1386:example := lwEdgeExp_holds 3 3 1 (le_refl 3) (1 / 2) 0 0 lwWx_inst_hE (le_refl 0) (by norm_num)
1391:example := lwEdgeExp_holds 3 3 2 (le_refl 3) 1 0 (1 / 2) lwWx_inst_hE (by norm_num) (by norm_num)
1418:example := oe1x_graph_E (sz := lwWxInstSz) (n := 0) (gaussIBP lwWxInstSz) lwWx_inst_im
1425:example := oe1x_graph_Ed (sz := lwWxInstSz) (n := 0) (gaussIBP lwWxInstSz) lwWx_inst_im
1464:example :
1484:example := oe1xT1_counters (mE 0) (oe1xInstGraph (mE 0)) oe1xInstP oe1xInst_mem 0 (Sum.inl 0) oe1xInst_hv
1485:example := oe1xT1_ord (mE 0) (oe1xInstGraph (mE 0)) oe1xInstP oe1xInst_mem 0 (Sum.inl 0) oe1xInst_hv
1486:example := owxT1_counters (mE 0) (oe1xInstGraph (mE 0)) 0
1487:example := owxT1_ord (mE 0) (oe1xInstGraph (mE 0)) 0
1488:example := oe1xDs_counters (mE 0) (oe1xInstGraph (mE 0)) oe1xInstP oe1xInst_mem 0 (Sum.inl 0) oe1xInstQr oe1xInst_memr
1489:example := oe1xDs_ord (mE 0) (oe1xInstGraph (mE 0)) oe1xInstP oe1xInst_mem 0 (Sum.inl 0) oe1xInstQr oe1xInst_memr
1490:example := oe1xDs_counters (mE 0) (oe1xInstGraph (mE 0)) oe1xInstP oe1xInst_mem 0 (Sum.inl 0) oe1xInstQb oe1xInst_memb
1491:example := oe1xDs_ord (mE 0) (oe1xInstGraph (mE 0)) oe1xInstP oe1xInst_mem 0 (Sum.inl 0) oe1xInstQb oe1xInst_memb
1492:example := oe1xDs_counters (mE 0) (oe1xInstGraph (mE 0)) oe1xInstP oe1xInst_mem 0 (Sum.inl 0) oe1xInstQf oe1xInst_memf
1493:example := oe1xDs_ord (mE 0) (oe1xInstGraph (mE 0)) oe1xInstP oe1xInst_mem 0 (Sum.inl 0) oe1xInstQf oe1xInst_memf
1497:example : (oe1xDs 1 (oe1xInstGraph 1) 0 (Sum.inl 0) oe1xInstQr).length = 2 ∧
1504:example := oe1x_integral (sz := lwWxInstSz) (n := 0) (gaussIBP lwWxInstSz) lwWx_inst_im
1525:example := oe1x_graph_E_loop (sz := lwWxInstSz) (n := 0) (gaussIBP lwWxInstSz) lwWx_inst_im
1531:example := oe1xT1loop_counters (mE 0) (oe1xInstGraphL (mE 0))
1535:example :
```
Target 1 at the ticket instance (lines 1376-1378: `(k₁,k₂,k₃,k₄) = (0,1,1,0)`, `P = 1`, `x = 0`, `y₁ = y′₀ = (1,0,0) ≠ x`, `w₀ = x`):
```
example := lwEdgeExp_holds 3 3 1 (le_refl 3) (1 / 2) 0 (1 / 2) lwWx_inst_hE (by norm_num) (by norm_num)
  0 1 1 0 (0 : Idx 3 3 1) ![Pi.single 0 1] ![Pi.single 0 1] ![0] ![] 1

```
Line 1381: `(1,1,1,1)`, `y₁ = x` (term `m 1_{x=y₁}` present), `f = Ḡ_{xx}`; 1386: `t = 0`; 1391: `W = 2`, `g = 1` (`N = 216`). Target 2: 1418 (`oe1x_graph_E`, graph `oe1xInstGraph`: `x, u` internal, `a, b, c, e` external; edges `G_{xa}` = `e₀`, `G_{xu}`, `Ḡ_{xb}`, `G_{cx}`, `Ḡ_{ex}`, `Ḡ_{ua}`, waved `S_{xu}`), 1425 (dotted form, `y₁ = u` internal), 1525 (`y₁ = x`); counters: computed by `decide` at 1464 (`Γ = (6,1,2,1)`, `oe1xT1 = (5,1,1)`, `owxT1 = (7,2,3,1)`, `oe1xP5 = oe1xP6 = oe1xD = (7,2,3,1)`, `oe1xP3 = oe1xP4 = (6,2,3,1)`) and by applying the counter theorems at 1484-1493, 1531, 1535; `oe1xDs` has 2, 2, 1 graphs for the red out-edge, the blue in-edge, the edge of `f` (1497).
### Name-clash grep of the new public names
```
$ for NAME in $(names.txt): git grep -nE "(theorem|def|abbrev|lemma|structure|instance)[[:space:]]+([A-Za-z_.]*\.)?NAME([[:space:]]|$|\()" main -- 'RBM3D/*.lean'
public names checked: 61; clash candidates on main (c24f54b): 0
$ git log --oneline f4cc46d..main ; git diff --name-only f4cc46d main | grep -v "^docs/"   # main since the branch base
c24f54b T2117: merge S1-26 Green/MinorDiffCond
d1cb5a6 T2112: merge S3-20 Induction/ZeroModeCalc
RBM3D.lean
RBM3D/Green/MinorDiffCond.lean
RBM3D/Induction/ZeroModeCalc.lean
$ git diff --stat f4cc46d main -- RBM3D/Test/Axioms.lean | wc -l
       0
```
No port from RBM1D/RBM2D: nothing was copied (the paper cites `(Oe1x)` from [yang2021] without proof; here it is proved from the Gaussian Stein identity `stein_sample`), so no `git diff --stat` for ports.
### Narrative (≤ 40 lines)
1. Verdict: both targets delivered. Target 1 `lwEdgeExp_holds : ∀ d, LWedgeExp d` (pin untouched: `Graph/LWPins.lean` has an empty diff). Target 2: `(Oe1x)` as a graph operation, with counters and `ord`, and the form for LW-08. New file `RBM3D/Graph/LWEdgeExp.lean` (1545 lines), registry line `RBM.Graph.LWedgeExp` removed from `RBM3D/Test/Axioms.lean`.
2. Core (`oe1x_integral`, sequence space): for every `C¹`-tame `f`, `E[G_{xy} f] = E[m δ_{xy} f + m (Σ_α S_{xα} Ǧ_{αα}) G_{xy} f - m Σ_α S_{xα} G_{αy} ∂_{h_{αx}} f]`. Proof as in the merged `owx_integral`: `stein_sample` on each `H_{xα} G_{αy} f`, the new resolvent identity `oe1x_resolvent_id` (`Σ_α H_{xα} G_{αy} = δ_{xy} + z G_{xy}`), `lwS_row_sum` (`Σ_α S_{xα} = t`) and `z + t m = -m⁻¹`; pathwise `G f - RHS = -m Z`, `E Z = 0`. There is no `S⁺`: `t m² G f` from the resolvent identity cancels `m² Σ_α S_{xα} G f` from `∂ G_{αy}` (the `Ǧ_{αα}` split `G_{αα} = Ǧ_{αα} + m`).
3. Target 1: `f := rest · f` with `oe1xR` (Finset products); `oe1x_dh_finprod` (Leibniz on `Finset.prod`) and `oe1x_dh_R` give the derivative of the rest from `dhSample_lwG` / `dhSample_lwG_star` (the `k₁`, `k₄` groups via `Finset.mul_prod_erase`); `oe1x_pointwise` (pure algebra, `Ḡ_{xx} = Ǧ̄_{xx} + m̄`, `G_{xx} = Ǧ_{xx} + m`) turns the sum into the nine pin terms; the bridge to `PF` is T2107's (`lwWx_integral`, `lwWx_lwPoly`, `lwWx_lwdf`, `lwWx_lwGc`, `lwWx_lwS_apply`, `lwWx_flow`, `lwWx_im_pos`). `t = 0`: `oe1x_lwG_zero` (`G = m I`) and `lwWx_lwS_zero`, both integrands equal `m δ_{xy₁} (rest · f)`.
4. Target 2: `oe1xT1d` (term 1 with the dotted edge `x = y₁`), `owxT1` (T2107, term 2, verbatim), `oe1xD q` (derivative graph of each solid edge `q.1` of `p.2`: `owxExt` + `owxDE` + the edge `G_{αy₁}`); `oe1x_term_integral` (one labelling), `oe1x_graph_Ed` (sum over labellings, via `owx_integral_val1`). Term 1 merged: `oe1xT1` is `relabel` onto `{i // i ≠ x}` (`oe1xPhi`), `oe1xT1_val` proves it has the value of `oe1xT1d` (reindexing of the sum over `ℓi`); `y₁ = x` is `oe1xT1loop` (`oe1x_graph_E_loop`).
5. Loops: for a red out-edge `q.1 = Ḡ_{xd}` (resp. blue in-edge `G_{sx}`) the derivative creates `Ḡ_{xx}` (resp. `G_{xx}`); `oe1xP5`, `oe1xP3` (resp. `oe1xP6`, `oe1xP4`) are the circled-loop graph and the graph with the constant `m̄` (resp. `m`); `oe1xD_red_term`, `oe1xD_blue_term`, `oe1xDs_integral`. `oe1xDs` is the list for each `q`; `oe1x_graph_E` is the final identity.
6. Counters (all proved): term 1 `Δ(n_S, n_W, n_V) = (-1, 0, -1)`, `Δ n_M ≤ 0` (`oe1x_nM_relabel_le`: `n_M` of a relabelling by an onto map fixing the external vertices), `Δord = +1`; term 2 `(1,1,1,0)`, `+1` (T2107); each `oe1xD`, `oe1xP5`, `oe1xP6`: `(1,1,1,0)`, `+1`; `oe1xP3`, `oe1xP4`: `(0,1,1,0)`, `Δord = 0` (the pull terms 3 and 4 of the table of T2040 (a)(i)). `Δord ≥ 0` for every term.
7. Form for LW-08: `oe1x_graph_E` for `v = y₁ ≠ x` (`hx : p.1 = ⟨true, false, inr x, v⟩`), `oe1x_graph_E_loop` for `y₁ = x`; `Sp` is an arbitrary matrix (no `S⁺`); `M_{aa} = m`, `0 < u`, `Im z > 0`, `z + u m = -m⁻¹`, `gaussIBP` proved. No definition outside `LWVocab` was needed for the counters (`relabel`, `owxExt`, `owxDE`, `lwSplit`, `lwStein_nM_congr`, `nM_eq_card` are merged).
8. Not stated: `(Oe1x)` for a circled `e₀ = Ǧ_{xy₁}`; counters of the merged form beyond `Δ n_M ≤ 0`.

## (c) Mathlib names verified (`lake env lean mlnames.lean`: 27 `#check @…` lines, 0 errors) and absent
`Finset.mul_prod_erase`, `Finset.erase_insert`, `Finset.erase_insert_of_ne`, `Finset.prod_insert`, `Finset.sum_image`, `Finset.sum_subset`, `Finset.sum_neg_distrib`, `Finset.sum_comm`,
`Fintype.card_subtype_compl`, `Fintype.card_subtype_eq`, `Fintype.card_pos_iff`, `Nat.card_le_card_of_injective`, `Function.surjInv`, `Function.injective_surjInv`, `Function.surjInv_eq`,
`SimpleGraph.ConnectedComponent.lift`, `SimpleGraph.ConnectedComponent.eq`, `SimpleGraph.Walk.reachable`, `star_sub`, `star_mul'`, `MeasureTheory.integral_congr_ae`, `integral_add`, `integral_sub`,
`integral_finsetSum`, `integrable_finsetSum`, `integral_const_mul`, `Fintype.sum_of_injective` (exists, unused).
Deprecated in this Mathlib (warnings at the first compile, replaced): `dif_neg` (use `dite_eq_right`/`simp`), `if_true` (use `ite_true`/`↓reduceIte`).

## (d) Open issues and paper-delta candidates
- **T2119a** (counter of term 1): the table of T2040 (a)(i) lists `Δ n_M = 0` for `Oe1x-delta` (`(-1, 0, -1, 0)`); Lean proves `Δ n_M ≤ 0` (`oe1xT1_counters`). Section (a) of this report (script `counters.py`) gives `-1` when `x` is merged into an external vertex or another internal molecule and `0` inside one molecule; the exact value is not proved here (the size `(L^d)^{n_M}` only needs `≤`).
- **T2119b** (terms 7, 8): section (a) (Verdicts, note 2) planned single graphs with coefficient `k₁ m`, `k₄ m`; Lean has one graph `oe1xD` per blue out-edge / red in-edge of `x` (each with coefficient `m`), because a graph's edges are a list; the pin keeps `k₁ m`, `k₄ m`. Same value (`oe1x_pointwise`).
- **T2119c** (terms 3-6): the unsplit derivative graph `oe1xD` has the uncircled loop `Ḡ_{xx}` / `G_{xx}` (`Δord = +1`); the paper's terms 3, 4 (`Δord = 0`) and 5, 6 are the split graphs of `oe1xDs` (`Ḡ_{xx} = Ǧ̄_{xx} + m̄`, `G_{xx} = Ǧ_{xx} + m`, hypothesis `M_{aa} = m`). The classification is by `(σ, src, dst)` of the differentiated edge (`oe1xDs`): a red loop at `x` is classed as a red out-edge, a blue loop at `x` as a blue in-edge.
- **T2119d** (`y₁ = x`): the merge of term 1 needs `y₁ ≠ x` (`hv`); for `y₁ = x` (`e₀` an uncircled loop `G_{xx}`, i.e. a weight) term 1 is `oe1xT1loop` with `Δ(n_S, n_V) = (-1, 0)`, `Δord = -1` (`oe1x_graph_E_loop`, `oe1xT1loop_counters`); the paper's table lists only the merged case.
- **T2119e** (scope): `(Oe1x)` is stated for `e₀` blue and uncircled (`hx`); the other edges `p.2` are arbitrary (circled ones included, `lwStein_dh_sedge_val`); a circled `e₀ = (G - M)_{xy₁}` is not stated. The pin `LWedgeExp` needs none of this (value-level).
- Observation: main moved from `f4cc46d` to `c24f54b` (T2112, T2117: new files and `RBM3D.lean` imports only); `RBM3D/Test/Axioms.lean` is unchanged on main since the base, so the one-line removal applies. The hub adds `import RBM3D.Graph.LWEdgeExp` at merge. After this ticket the registry ledger still lists `LWggExp` (LW-07) as owed.
- No change to `(a)`; no `(a′)` section: nothing in (a) was wrong (note 2 of the Verdicts is the planning remark answered by T2119b).
- All targets delivered: `all_targets_done = true`.
