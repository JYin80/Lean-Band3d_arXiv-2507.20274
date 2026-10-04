Auditor model: claude-opus-5-5
# T2120 audit (round 1) — LW-07 `(Oe2x)`: `lwGGExp_holds`, `(Oe2x)` as a graph operation
Audit started: Sun Oct  4 07:52:50 UTC 2026 (`date -u`). Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2120-audit1`, detached at `c7fd80a` (= `t/T2120`), merge-base with `main` `d1cb5a6`.

## 1. Build, axioms, hygiene, diff
```
$ lake build RBM3D.Graph.LWGGExp RBM3D.Test.Axioms 2>&1 | tail -1
Build completed successfully (3363 jobs).
$ lake env lean RBM3D/Graph/LWGGExp.lean 2>&1 | grep -cE "error|warning"
0
$ git diff --stat main...t/T2120
 RBM3D/Graph/LWGGExp.lean | 1748 ++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean   |    1 -
$ git diff main...t/T2120 -- RBM3D/Test/Axioms.lean | grep -E "^[-+][^-+]"
-   `RBM.Graph.LWggExp, -- `(Oe2x)` (`7_8:334-349`): LW-07
$ git diff main...t/T2120 -- RBM3D/Graph/{LWPins,LWWeightExp,LWVocab,LWStein}.lean | wc -l     # pin and merged files untouched
       0
$ git diff main...t/T2120 | grep -nE "^\+.*\b(sorry|admit|native_decide)\b|^\+axiom " | wc -l
       0
```
`#print axioms` (scratch file `scratchpad/T2120/audax.lean`, `import RBM3D.Graph.LWGGExp`, run with `lake env lean`; verbatim, one per line):
```
'RBM.Graph.lwGGExp_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.oe2x_graph_E' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.oe2x_term_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.oe2x_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.oe2xR{1,2,4,5,6,7,8}_counters' depends on axioms: [propext, Classical.choice, Quot.sound]   (7 lines, identical)
'RBM.Graph.oe2xR{1,2}_nM_ge' depends on axioms: [propext, Classical.choice, Quot.sound]                  (2 lines, identical)
'RBM.Graph.oe2xR{1,2,4,5,6,7,8}_ord' depends on axioms: [propext, Classical.choice, Quot.sound]        (7 lines, identical)
'RBM.Graph.oe2xR1_val' depends on axioms: [propext, Classical.choice, Quot.sound]
lwGGExp_holds : ∀ (d : ℕ), LWggExp d
```
Sole writable files: exactly `RBM3D/Graph/LWGGExp.lean` (new) and `RBM3D/Test/Axioms.lean` (one registry line removed). The new file imports only `Graph/{LWPins,LWStein,LWVocab,LWWeightExp}`, `Gauss/FineModel`, `Green/IBPPoly`, `Mathlib.Algebra.MvPolynomial.Rename` (no `import RBM3D`). Full `lake build` is the hub's at merge (`main` has one later merge, `c24f54b`, touching `Green/MinorDiffCond` and `RBM3D.lean` only).

## 2. Target 1 — `lwGGExp_holds : LWggExp d` — PASS
**Statement.** The theorem's type is literally the merged pin (`#check (lwGGExp_holds : ∀ d, LWggExp d)` above), and `LWPins.lean` is unchanged on the branch (diff 0 lines), so no script diff of statement text is needed: the target equals the pin as fixed by §34. Pin vs paper (`paper/tex/7_8_light_weight.tex`, lemma `T eq0`, eq. `(Oe2x)`), term by term (pin at `LWPins.lean:164-183`):
```
paper (Oe2x)                                              | pin LWggExp
m δ_xy G_y'x f                                            | mE E * (if x = y then 1 else 0) * lwG y' x * lwf
m³ S⁺_xy G_y'y f                                          | mE E^3 * lwSp x y * lwG y' y * lwf
m Σ_α S_xα Ǧ_αα 𝒢                                         | mE E * (Σ α, lwS x α * lwGc α α) * (lwG x y * lwG y' x * lwf)
m³ Σ S⁺_xα S_αβ Ǧ_ββ G_αy G_y'α f                         | mE E^3 * ΣΣ lwSp x α * lwS α β * lwGc β β * lwG α y * lwG y' α * lwf
m Ǧ_xx Σ S_xα G_αy G_y'α f                                | mE E * lwGc x x * Σ lwS x α * lwG α y * lwG y' α * lwf
m³ Σ S⁺_xα S_αβ Ǧ_αα G_βy G_y'β f                         | mE E^3 * ΣΣ lwSp x α * lwS α β * lwGc α α * lwG β y * lwG y' β * lwf
- m Σ S_xα G_αy G_y'x ∂_{h_αx} f                          | - mE E * Σ lwS x α * lwG α y * lwG y' x * lwdf P ω α x
- m³ Σ S⁺_xα S_αβ G_βy G_y'α ∂_{h_βα} f                   | - mE E^3 * ΣΣ lwSp x α * lwS α β * lwG β y * lwG y' α * lwdf P ω β α
```
Quantifiers: `∀ L W [NeZero L] [NeZero W], 3 ≤ L → ∀ g E t, |E| < 2 → 0 ≤ t → t < 1 → ∀ x y y' P`, `=_E` read as equality of `∫ … ∂(PF d L W g)`; matches DECISIONS §29 ranges (every `g`, `L ≥ 3`, `W ≥ 1`, `|E| < 2`, `0 ≤ t < 1`, every `d`). The `t = 0` case is included (`oe2x_lwG_zero`), not split off.
**Vacuity / hidden hypotheses / cycles.** No hypothesis beyond the pin; the proof uses the merged `gaussIBP` (DECISIONS-authorized Gaussian IBP, limit check T2107's) and T2107's bridge (`lwWx_*`, merged in `LWWeightExp`). No structure field carries a hypothesis; dependencies are merged files only (imports above). No cycle: the pin lives in `LWPins`, the proof in the new file.
**Compiled nonempty instances** (in the file, compiled by the build above):
```
1629: example := lwGGExp_holds 3 3 1 (le_refl 3) (1 / 2) 0 (1 / 2) lwWx_inst_hE (by norm_num) (by norm_num)
  (0 : Idx 3 3 1) (Pi.single 0 1) (Pi.single 0 1) 1
1633: example := lwGGExp_holds 3 3 1 (le_refl 3) (1 / 2) 0 (1 / 2) lwWx_inst_hE (by norm_num) (by norm_num)
  (0 : Idx 3 3 1) (Pi.single 0 1) 0 (MvPolynomial.X (true, (0 : Idx 3 3 1), 0))
1639: example (x y y' : Idx 3 3 2) := LWInstFixed.inst_gg (lwGGExp_holds 3) x y y'
```
Ticket's data exactly (`d=3, L=3, W=1, g=1/2, E=0, t=1/2, P=1`), `N = 27`, `x ≠ y`; every hypothesis (`3 ≤ L`, `|E|<2`, `0 ≤ t`, `t < 1`) discharged; the second example uses a non-constant `f` (derivative terms live), the third discharges the merged `inst_gg`'s pin hypothesis.

## 3. Target 2 — `(Oe2x)` as a graph operation — PASS
**Statement** (extracted from file, `RBM3D/Graph/LWGGExp.lean:1550`):
```
theorem oe2x_graph_E (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) {m : ℂ}
    (hm0 : m ≠ 0) (hzm : z + (u : ℂ) * m = -m⁻¹) (Sp M : Matrix …)
    (hSp : ∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j) (hM : ∀ a, M a a = m)
    (Γ : LGraph E I) (x : I) (y y' : E ⊕ I) (hy : y ≠ Sum.inr x)
    (p …) (hp : p ∈ lwSplit Γ.solid) (hp1 : p.1 = ⟨true, false, Sum.inr x, y⟩)
    (q …) (hq : q ∈ lwSplit p.2) (hq1 : q.1 = ⟨true, false, y', Sum.inr x⟩) (ℓe : E → Idx …) :
    ∫ Γ.val = ∫ R1.val + ∫ R2.val + ∫ (owxT1 m Γ x).val + ∫ R4.val + ∫ R5.val + ∫ R6.val
              + Σ_{q' ∈ lwSplit q.2} ∫ R7_{q'}.val + Σ_{q' ∈ lwSplit q.2} ∫ R8_{q'}.val      (all ∂ Sizes.seqP sz)
```
The eight term graphs (`oe2xR1` merge `x ↦ y` with coefficient `m`; `oe2xR2` coefficient `m³`, edges `G_{y'y}`, blue waved `S⁺_{xy}`; `R3 = owxT1`; `oe2xR4/R5/R6` with `owxEmb 2/1/2`; `oe2xR7/R8` one graph per solid edge of `f` via `owxDE`) were read at `LWGGExp.lean:485-570` and match the eight terms of `(Oe2x)` in coefficient, edge set and new summed vertices. The data hypotheses (`hz`, `hu`, `hzm`, `hSp`, `hM`, `GaussIBP`) and the `Sizes.seqP` setting are identical to the merged twin `owx_graph_E` (`LWWeightExp.lean:1316-1320`), i.e. the form LW-08 already consumes for `(Owx)`.
Counters (conclusions, extracted): `R1: nS+1=Γ.nS, nW=, nV+1=Γ.nV, nM ≤ Γ.nM` (+ `oe2xR1_nM_ge`: `Γ.nM ≤ nM+1`); `R2: nS+1=Γ.nS, nW=Γ.nW+1, nV=, nM ≤` (+ `_nM_ge`); `R4,R6,R8: (+1,+2,+2,=)`; `R5,R7: (+1,+1,+1,=)`; `R3 = owxT1` merged counters; `oe2xR{1,2,4,5,6,7,8}_ord : ord … = ord Γ.counters + 1`. Matches T2040 b.9 row LW-07 for `nS,nW,nV,ord`; `nM` differs for R1/R2 (see §4, `T2120a`). No definition outside `LWVocab`/`LWStein`/`LWWeightExp` is used (stop condition not triggered).
**Hypotheses.** `hy : y ≠ Sum.inr x` (vertex `y` distinct from the internal `x`; labels may still coincide — `δ_xy` is the merge) and `hp1/hq1` (blue, no circle) restrict to the lemma's setting `G_{xy} G_{y'x}` with two vertices; the diagonal case `y = x` is a weight (`G_xx`), handled by `(Owx)`; recorded as candidate `T2120b`. `y'` is unrestricted (`y' = x` allowed). `hSp` is satisfiable (merged `lwSplus_spec`), not vacuous. No hidden hypothesis in a structure field.
**Compiled nonempty instances** (`LWGGExp.lean:1643-1748`): graph `Γ = G_{xa} G_{bx} G_{aw} Ḡ_{wb}` with waved `S_{xw}` (`E = I = Fin 2`, `f` with two solid edges, so R7/R8 are two graphs each):
```
1671: example := oe2x_graph_E (sz := lwWxInstSz) (n := 0) (gaussIBP lwWxInstSz) lwWx_inst_im
  (by norm_num : (0 : ℝ) < 1 / 2) (lwWx_mE_ne 0 lwWx_inst_hE) (lwWx_flow 0 (1 / 2) lwWx_inst_hE)
  lwWxInstSp lwWxInstM lwWx_inst_hSp lwWx_inst_hM (oe2xInstGraph (mE 0)) 0 (Sum.inl 0) (Sum.inl 1)
  oe2xInst_hy oe2xInstP (oe2xInst_hp _) rfl oe2xInstQ oe2xInst_hq rfl (fun _ => 0)
```
`lwWxInstSz = lwWxSizes 3 3 1 (1/2) (le_refl 3)` (`LWWeightExp.lean:1382`: `d=3, L=3, W=1, g=1/2`), `E=0`, `u=1/2`; every hypothesis discharged by merged or local proofs (no hypothesis left open). Line 1678: all eight `_ord` theorems applied at the instance; line 1705: the `nM` bounds; line 1719: the counters of `Γ` and of every term by `decide` (`Γ (4,1,2,1)`, `R1 (3,1,1,0)`, `R2 (3,2,2,0)`, `R3/R5/R7 (5,2,3,1)`, `R4/R6/R8 (5,3,4,1)`), nondegenerate (nonempty internal index, `x ≠ y` vertices, two solid edges in `f`).

## 4. Paper-delta coverage
Lean/paper differences and their candidates (proposed in `T2120-prove.md` (d)):
- `=_E` read as equality of expectations on `PF`/`seqP`; `f` a resolvent polynomial; `S⁺` via `(g,E,t)` of §34; `∂_{h_{αx}} = dhSample` — `T2120c`.
- Graph form needs `y ≠ x` as vertices for R1 — `T2120b`.
- `nM` of R1/R2 may drop by one (T2040 table says `0`) — `T2120a` (a delta against T2040's table, not against the paper; the paper's "do not create new molecules" is consistent with a drop).
- `f` as the product of the other solid edges, one R7/R8 graph per edge — `T2120d`.
Coverage is complete for every statement difference found.

## 5. Observations (no verdict change)
- O1. The graph-level identity `oe2x_graph_E` assumes `0 < u` (as the merged `owx_graph_E` does); the `t = 0` case is covered only at the pin level (target 1). Not a ticket requirement for target 2; the dispatcher may add it to `T2120c` if LW-08 ever needs `t = 0` graph-level.
- O2. Only the `G G` form is stated (`hp1/hq1` blue); the paper derives `Ḡ Ḡ` by conjugation (`7_8:341`), same as the paper's lemma.
- O3. In the graph instance the external labels are `fun _ => 0` (`a`, `b` at the same lattice point); the identity is still a nontrivial sum over the 27² internal labels.

## Verdict
- Target 1 `lwGGExp_holds`: **PASS**.
- Target 2 `oe2x_graph_E` + counter/`ord` theorems: **PASS**.
Ticket T2120: **PASS**. No dispatcher sign-off needed.
