Auditor model: claude-opus-5-5

# T2060 audit (round 1) — LW-04 Stein bridge, `RBM3D/Graph/LWStein.lean`
Date (`date -u`): Sat Oct  3 16:09:15 UTC 2026. Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2060-audit1`, detached at `t/T2060` = `9ec0e8c`.
`S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2060`.

## 1. Scope, build, hygiene
```
$ git diff --stat main...t/T2060
 RBM3D/Graph/LWStein.lean | 1983 ++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean   |    1 +
$ git diff main...t/T2060 -- RBM3D/Test/Axioms.lean | grep '^[+-]'   (hunk @@ -155,6 +155,7 @@ def structuralProps)
+   `RBM.Graph.Tame1,          -- `F` is `C¹`-tame (...): hypothesis of `stein_sample`; proved for resolvent polynomials by `lwPoly_tame1` (T2060)
$ lake build RBM3D.Graph.LWStein   (audit worktree; no LWStein olean in the copied cache)
✔ [3320/3320] Built RBM3D.Graph.LWStein (6.1s)
Build completed successfully (3320 jobs).            exit=0   (no error/warning line for LWStein)
$ lake build RBM3D.Test.Axioms
✔ [2/2] Built RBM3D.Test.Axioms (1.3s)
Build completed successfully (2 jobs).
$ grep -nE "sorry|admit|native_decide|^ *axiom " RBM3D/Graph/LWStein.lean ; echo $?
1
$ lake env lean $S/audit_registry.lean   # import RBM3D; import RBM3D.Graph.LWStein; #assert_rbm_axioms
exit 0   (no duplicate-declaration error, no "unregistered premise"); line 81: RBM.Graph.Tame1 (structural)
$ grep -n import RBM3D/Graph/LWStein.lean
6:LWVocab 7:Expansions 8:Green.LDEQuad 9:Gauss.FineModel 10:Gauss.FlowCalculus 11:Mathlib...MvPolynomial.Basic 12:Mathlib...Gershgorin
$ grep -rn "import RBM3D.Graph.LWStein" RBM3D    -> (none; no cycle)
```
Frozen signatures: no merged file touched. All imports are merged modules; never `RBM3D`.

## 2. Axioms (`lake env lean $S/ax.lean`, sorted)
```
owx_defect_identity owx_smallest owx_second owx_smallest_E dhSample_lwG dhSample_lwG_star dhSample_lwG_eq_deriv
lwPoly_tame1 stein_sample stein_lwPoly integral_owxDefect owx_integral lwSplus_spec dhSample_graphVal
LGraph.dTerm_counters LGraph.dTerm_ord LGraph.dTerms_counters LWInstOwx.inst_owx_smallest_E_unit
  -> each: depends on axioms: [propext, Classical.choice, Quot.sound]   (18 of 18)
```

## 3. Target 1 — verbatim copy of probe section 4 (lines 433–698, `end OwxSmallest`)
```
$ git --no-optional-locks show eeda441:RBM3D/Probe/T2040Graphs.lean > $S/probe.lean
$ diff <(sed -n 433,697p probe.lean) <(sed -n 84,348p LWStein.lean); echo $?      -> 0
$ sed -n 698,699p probe.lean; sed -n 729,730p probe.lean   (skipped block = candidate B)
  (blank) / "/-! ### Candidate B on the same identity ..." ... (blank) / "end OwxSmallest"
$ sed -n 349p LWStein.lean -> end OwxSmallest
$ diff <(sed -n 2033,2112p probe.lean) <(sed -n 1902,1981p LWStein.lean); echo $?  -> 0   (LWInstOwx instances)
```
Changes forced by `LWVocab`: none (text-identical). **PASS.**

## 4. Target 2 — the derivative and its closed forms
`dhSample` (l.521), checked against the merged model: `coordinateMatrix (a,b,true) = E_ab+E_ba`, `(a,b,false) = iE_ab − iE_ba`
for `key a<key b`, `(a,a,true) = E_aa` (proved here: `lwStein_coordMat_true_lt/false_lt/diag`), so `(∂_a − i∂_b)/2` on
`(α,w,·)` is `∂/∂X_{αw}` with `X_{wα}` held fixed (Wirtinger); the `key w<key α` branch is its conjugate orientation; the
diagonal is `∂_a`. Scaling `(√u)⁻¹`: `h = √u X`. The convention is tied to the merged complex-line derivative by
```
627| theorem dhSample_lwG_eq_deriv ... (hu : 0 < u) ... :  dhSample ... (lwG ... i j) ω =
       deriv (fun s : ℂ => Ring.inverse ((seqHflow n u ω − z•1) + s • single α w 1) i j) 0
561| theorem dhSample_lwG  (hz : 0 < z.im) (hu : 0 < u) (α w i j) (ω) : dhSample sz n u α w (lwG sz n z u i j) ω = -(G_iα * G_wj)
591| theorem dhSample_lwG_star (hz) (hu : 0 < u) ... : dhSample ... (fun ω => star (G_ij ω)) ω = -star (G_iw * G_αj)
```
Ticket pin: `∂G_ij = −G_iα G_wj`, `∂Ḡ_ij = −conj(G_iw G_αj)`, `G = (H_u−z)⁻¹`, `Im z>0`, √u of the flow: matches; all
`α,w,i,j`, including `α = w`. Extra hypothesis `0 < u` (at `u = 0`, `H_0 = 0` does not depend on `h`); stated in the
docstring of `dhSample` and in narrative 2 / T2060a. Instances: l.1696 (`d=3,L=3,W=2`, `u=7/10`, `z=0.3+0.05i`, every ω)
and l.1708 (fixed sample `lwOmega`, vertices `0`, `(1,0,0)`), l.1758 (convention vs complex derivative at `lwOmega`). **PASS.**

## 5. Target 3 — complex Stein on the model
```
998| def lwS (u : ℝ) := Matrix.of fun i j => ((u * svarF d (L n) (W n) (lam n) i j : ℝ) : ℂ)        -- S^{(u)} = u·svarF
703| structure Tame1 (sz) (n) (F) : Prop where tame : Tame sz F; diff : ∀ c ω, DifferentiableAt ℝ (t ↦ F (update ω ⟨n,c⟩ t)) (ω ⟨n,c⟩);
       tame_partial : ∀ c, Tame sz (lwPartial sz n c F)
949| def lwPoly (z) (u) (P : MvPolynomial (Idx × Idx × Bool) ℂ) (ω) := MvPolynomial.eval (fun v => lwVar ...) P   -- (i,j,true)=G_ij, false=star G_ij
965| theorem lwPoly_tame1 (hz : 0 < z.im) (u : ℝ) (P) : Tame1 sz n (lwPoly sz n z u P)
1013| theorem stein_sample (hG : GaussIBP sz) {F} (hF : Tame1 sz n F) {u} (hu : 0 ≤ u) (α w) :
       ∫ ω, sz.seqHflow n u ω w α * F ω ∂seqP = lwS sz n u w α * ∫ ω, dhSample sz n u α w F ω ∂seqP
1108| theorem stein_lwPoly (hG : GaussIBP sz) (hz : 0 < z.im) (hu : 0 ≤ u) (P) (α w) :
       ∫ ω, seqHflow n u ω w α * lwPoly P ω = lwS sz n u w α * ∫ ω, dhSample sz n u α w (lwPoly P) ω
```
Pin `E[(H_u)_{wα}F] = S^{(u)}_{wα} E[∂_{h_{αw}}F]`, every `w, α` incl. `w = α`, `F` a resolvent polynomial (D64 = T2040d
class), `GaussIBP` as hypothesis only: matches. `Tame1` is a hypothesis of `stein_sample` only and is discharged for every
resolvent polynomial (`lwPoly_tame1`), so `stein_lwPoly` carries only `GaussIBP` (owed, registered; another gate's pin).
Variances: `lwStein_gvar_off` (`S/2`, `i ≠ j`), `lwStein_gvar_diag` (`S_ii`) are proved from the merged `gvarF`; the ticket's
stop condition (variance mismatch) did not occur. Instances at `sz0` (`L=4, W=32`, `n=0`, `u=1/2`, `z=7i/4`), hypothesis
`GaussIBP sz0` only: l.1768 (`F = G_xx`, all `x,w,α`), l.1778 (pair `w=0`, `α=(32,0,0)`), l.1788 (`F = G_xy Ḡ_xy`);
tameness instance l.1746 (`|G_00|²+2` at `lwSzT`). **PASS.**

## 6. Target 4 — `E Z_w = 0` and `(Owx)` in expectation
```
1136| theorem integral_owxDefect (hG : GaussIBP sz) (hz : 0 < z.im) (hu : 0 < u) (P) (w) :
       ∫ ω, owxDefect z (lwGm sz n z u ω) (lwS sz n u) (lwPoly P ω) (fun α w' => dhSample sz n u α w' (lwPoly P) ω) w = 0
1239| theorem owx_integral (hG) (hz : 0 < z.im) (hu : 0 < u) {m} (hm0 : m ≠ 0) (hzm : z + u*m = -m⁻¹) (Sp)
       (hSp : ∀ i j, Sp i j - m^2 * ∑ w, Sp i w * lwS u w j = lwS u i j) (P) (x) :
       ∫ (G_xx − m)·f = ∫ (m Σ_α S_xα Ǧ_xx Ǧ_αα f + m³ Σ_αβ Sp_xα S_αβ Ǧ_αα Ǧ_ββ f − m Σ_α S_xα G_αx ∂_{h_αx} f − m³ Σ_αβ Sp_xα S_αβ G_βα ∂_{h_βα} f)
```
`owxDefect` (item 1) = `(1+zG_ww)f + (Σ_α S_wα G_αα)G_ww f − Σ_α S_wα G_αw df α w`; with `df = dhSample` this is
`Σ_α H_wα G_αw f − Σ_α S_wα ∂_{h_αw}(G_αw f)` by the resolvent identity and `∂_{h_αw}G_αw = −G_αα G_ww`: the pin. No
integrability hypothesis (derived from `Tame1`). `owx_integral` is the general-`f` form of the probe's `owx_smallest_E`
with the same deterministic hypotheses (`m ≠ 0`, `z + s m = −1/m` with `s = u`, `S⁺(1−m²S) = S`); the row-sum hypothesis
is discharged by `lwS_row_sum` (no hypothesis). Instances at `sz0`: l.1793 (`E Z_w = 0`, `f = G_xx`), l.1803 (`(Owx)` with
`m = i/2`, `z = 7i/4`, `u = 1/2`; `hzm` by `lwM0_hzm`, `hSp` by `lwSplus_spec` from `|m|²u = 1/8 < 1`; only `GaussIBP sz0`
remains). Nondegenerate (`N = (4·32)³`, `m ≠ 0`, `Im z > 0`). **PASS.**

## 7. Target 5 — the graph derivative
```
1374| def lwDEdges (e) := if e.σ then (⟨true,false, e.src, α⟩, ⟨true,false, w, e.dst⟩) else (⟨false,false, e.src, w⟩, ⟨false,false, α, e.dst⟩)
1381| def LGraph.dTerm (Γ) (p) : LGraph (E ⊕ Fin 2) I := solid := p.2.map emb ++ [lwDEdges p.1]; waved, dotted mapped; coeff := −Γ.coeff
1390| def LGraph.dTerms (Γ) := (lwSplit Γ.solid).map Γ.dTerm
1562| theorem dhSample_graphVal (hz : 0 < z.im) (hu : 0 < u) (Γ : LGraph E I) (ℓe) (α w) (ω) :
       dhSample sz n u α w (fun ω => Γ.val (lwSampleData sz n z u M S Sp ω) ℓe) ω =
       (Γ.dTerms.map fun Γ' => Γ'.val (lwSampleData ... ω) (Sum.elim ℓe ![α, w])).sum
1619| theorem LGraph.dTerm_counters (hp : p ∈ lwSplit Γ.solid) : nS = Γ.nS + 1 ∧ nW = Γ.nW ∧ nV = Γ.nV ∧ nM = Γ.nM
1656| theorem LGraph.dTerm_ord ... : ord (Γ.dTerm p).counters = ord Γ.counters + 1
```
Merged `SEdge.val` (LWVocab:115): `g = G_ab − [circ]·M_ab`, red = `star g`. Blue `G_ab ↦ −G_aα G_wb`, red
`Ḡ_ab ↦ −Ḡ_aw Ḡ_αb` = `−conj(G_aw G_αb)`: matches item 2; the circle (light-weight `G − M`, `M` constant) is dropped, so
`Ǧ` has the derivative of `G`. One term per solid edge (weights and light-weights included), arbitrary `M, S, Sp`. New
vertices `α, w` are external (`E ⊕ Fin 2`), counters `n_S + 1`, others unchanged: as pinned; delta T2060d. Instances:
l.1843 `owxG1` at `sz0` (2 terms, each `nS=3,nW=1,nV=1,nM=0`), l.1860 two-edge graph `S_xa G_xa Ḡ_ay` at `lwSzT`,
l.1877 merged `figGraph` (8 terms, `nS=9`). All deterministic hypotheses discharged. **PASS.**

## 8. Paper-delta coverage
| Lean/paper difference | coverage |
|---|---|
| `∂_{h_{αw}}` undefined in §7; Wirtinger convention in real coordinates, `0 < u` | D65 (T2040i) + candidate T2060a (prove report (d)); `0<u` in `dhSample` docstring |
| `f` = resolvent polynomial (paper: differentiable function of `G`) | D64 (T2040d), cited |
| `=_𝔼` read as equality of integrals; flow data `S = u·svarF`, `z+um = −1/m` | T2060b (and T2040e) |
| model variances, `u ≥ 0`, `GaussIBP` as hypothesis | T2060c |
| derivative graphs with `α, w` as new external vertices | T2060d |
| `S⁺` taken as any `Sp` with `Sp(1−m²S) = S` | T2060e |
Every statement difference found above is covered.

## 9. Observations (no statement, instance, build, axiom or delta effect)
- O1. Imports beyond the ticket's list: `RBM3D.Gauss.FlowCalculus` (merged) and two Mathlib modules; disclosed in narrative 7.
- O2. The preflight's `figAux` (an `NGraph`, no values) is replaced by the merged `figGraph`; the ticket's Lean instances
  (owxG1, two-edge graph) are both present.
- O3. `0 < u` of the closed forms could be stated explicitly inside the T2060a text when the dispatcher numbers it.
- O4. The branch base is `c1d4ebe`; `main` is now `aa42e43`; the hub's full build at merge covers the newer main.

## Verdict
Targets 1–5: **PASS**. No dispatcher sign-off needed.
