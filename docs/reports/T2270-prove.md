Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 08:20:36 UTC 2026

### (i) Exponent table
Notation: `r_j = |a_j-b_j|`, `|P_j|` = path length, `rest = anpKey5_rest Γ M`. Columns: figAux / figIVext / figAuxGh / oneEdge (q=0). Numbers are the rows of `s0.py`/`s3.py`/`s4.py` (output in (ii)).
| quantity | values | constraint | slack |
|---|---|---|---|
| (p, q) | (2,2) / (2,1) / (2,2) / (1,0) | `q ≤ p`; `IsNested`, `GhostOK` hold (s0) | n/a |
| `nSolid, nngh, ordN` | 6,2,2 / 4,0,2 / 4,0,0 / 1,1,1 | `ordN = nSolid-2q` | 0 |
| `|rest|` and `|rest|+nngh = nSolid` | 4 (+2=6) / 4 (+0=4) / 4 (+0=4) / 0 (+1=1) | identity for `M ∈ 𝓜` (M = one edge per ghost-free path, edge-disjoint, all solid) | 0 |
| exponent of `ψ(0)`: `ordN-nngh = |rest|-2q` | 0 / 2 / 0 / 0 | `≥ 0`: an order gives `≥ 2` list positions per vertex, an edge counted only at its later end, so `|E| ≥ 2q` | 0 / 2 / 0 / 0; min over 1363 graphs: 0 (s4) |
| exponent of `θ` | 2 / 1 / 2 / 0 | `= q` (one `Σ_x ξξ ≤ θ` per vertex) | 0 |
| `|𝓜|` vs `C = Π_j max(1,|P_j|)` (all j) | 9 ≤ 9 / 1 ≤ 6 / 1 ≤ 9 / 1 ≤ 1 | `|𝓜| ≤ #choice fns ≤ C` | 0 / 5 / 8 / 0 |
| `c = 1/(1+Σ_j|P_j|)` | 1/7 / 1/6 / 1/7 / 1/2 | `0 < c ≤ 1`, `c ≤ 1/|P_j|` for ghost-free `j` | figAux 1/3-1/7 = 4/21; oneEdge 1/2; ghost paths: none needed |
| long-edge chain per ghost-free `j` | `c r_j ≤ r_j/|P_j| ≤ len(e_j)`, so `ξ_e ≤ ψ(len) ≤ ψ(c r_j)` | `anpKey_long_edge`: `r_j ≤ |P_j| len`; `ψ` antitone on `[0,∞)` | factor `(1+Σ)/|P_j|` in `c`: figAux 7/3 |
| certificate depth of `rest(M)` | 0..1 / 0 / 0 / 0 | `≤ ⌊q/2⌋` | figAux 0 (depth 1 attained); s4: 0 violations, (q,depth) {(2,1):29,(3,1):21} |
| AM-GM weights | `½+½ = 1` | both leaf lists have length `|E|` (`E.set`), `2 ξ_kξ_k' ≤ ξ_k²+ξ_k'²` | 0 |
| ratio `val/(C θ^q ψ(0)^{ordN-nngh} Π ψ(c r_i))`, d=3, L=3 / L=5 | s0: figAux .0494/.0256; figIVext .0627/.0281; figAuxGh .1095/.1051; oneEdge 1.0000/.7788 | `≤ 1` | oneEdge 0 (equality at `a=b`) |
Observation: for figIVext (both paths ghost) the ticket writes `C = 1` (card of `𝓜`); the pin only needs `|𝓜| ≤ Π_j max 1 |P_j|` over all `j`, which is 6 there; both are fine.

### (ii) Concrete nondegenerate instance
Data: `d = 3`, `L = 3` (27 sites), `ψ(r) = 1/(1+r)`, `θ = 1`, `ξ ≡ 1/6`, `a ≡ 0`, `b ≡ (1,1,1)` (`|a-b| = 1`), graphs figAux, figIVext, figAuxGh, oneEdge (all `IsNested`, `GhostOK`); every deterministic hypothesis checked below in exact rationals. Scratch `<scratchpad>/T2270/` (`lib.py g.py graphs.py` copied from T2264's scratch, `u.py` new; Python only).
```
$ python3 s0.py   # rows of the table (i)
graph | nested GhostOK | p q nSolid ordN nngh | |M| (choice fns) | C=prod max(1,|P_j|) | c=1/(1+sum|P_j|) | |rest| set | ordN-nngh | depths | |rest|-2q | facts(perPath,|rest|+nngh=nSolid,|M|<=C)
figAux | True True | 2 2 6 2 2 | 9 | 9 | 1/7 | [4] | 0 | [0, 1] | [0] | True
figIVext | True True | 2 1 4 2 0 | 1 | 6 | 1/6 | [4] | 2 | [0] | [2] | True
figAuxGh | True True | 2 2 4 0 0 | 1 | 9 | 1/7 | [4] | 0 | [0] | [0] | True
oneEdge (q=0) | True True | 1 0 1 1 1 | 1 | 1 | 1/2 | [0] | 0 | [0] | [0] | True
ratio val/(C theta^q psi(0)^(ordN-nngh) prod_{ghost-free} psi(c r_i)), d=3, random xi (tight/rand/sparse/near), 4 psi, theta factor 1,1.7, 3 (a,b) each
  figAux         L=3: 96 cases, violations 0, max ratio 0.0494
  figAux         L=5: 96 cases, violations 0, max ratio 0.0256
  figIVext       L=3: 96 cases, violations 0, max ratio 0.0627
  figIVext       L=5: 96 cases, violations 0, max ratio 0.0281
  figAuxGh       L=3: 96 cases, violations 0, max ratio 0.1095
  figAuxGh       L=5: 96 cases, violations 0, max ratio 0.1051
  oneEdge (q=0)  L=3: 96 cases, violations 0, max ratio 1.0000
  oneEdge (q=0)  L=5: 96 cases, violations 0, max ratio 0.7788
$ python3 s3.py
hypotheses at the instance: L=3 (NeZero), d=3, sites 27 | max zdistInf 1 | psi(r)=1/(1+r) >0 and antitone on [0,inf) (1/(1+r)-1/(1+s)=(s-r)/((1+r)(1+s))>=0 for r<=s)
 xi symmetric >=0 (constant): True | xi<=psi(dist): 1/6 <= psi(1)= 1/2 : True | row sum of xi^2 = 3/4 <= theta = 1 : True | zdistInf(a-b) = 1 (a=0,b=(1,1,1))
 figAux: p,q=2,2 nested True GhostOK True | |M|=9 C=9 c=1/7 | val=1/64=0.015625 <= union RHS 3.87598 <= bound 6.89062 : True
 figIVext: p,q=2,1 nested True GhostOK True | |M|=1 C=6 c=1/6 | val=1/48=0.0208333 <= union RHS 0.0208333 <= bound 6 : True
 figAuxGh: p,q=2,2 nested True GhostOK True | |M|=1 C=9 c=1/7 | val=9/16=0.5625 <= union RHS 0.5625 <= bound 9 : True
 oneEdge: p,q=1,0 nested True GhostOK True | |M|=1 C=1 c=1/2 | val=1/6=0.166667 <= union RHS 0.666667 <= bound 0.666667 : True
 sum pin at the depth-1 certificate rest(figAux,{0,5}) (|E|=4,q=2, no order): 9/16 = 0.5625 <= theta^2 psi(0)^0 = 1 : True | certificate literal: True
 order pin at rest(figIVext,{}) (|E|=4,q=1, order [0]): 1/48 = 0.020833333333333332 <= theta^1 psi(0)^2 = 1 : True | sumOrder literal: True
```
Sum/order pins at random data (`AnpKey6OrderPin`, `AnpKey6SumPin`: certificates of figAux, figAuxGh, figIVext, figAux^k up to depth 3 (all 8 depth-3 lists), plus random edge lists with loops, external-external edges, parallel edges; d in {1,2,3}, L in {3,5,7}, 4 envelopes incl. `ψ(0) ≠ 1`, up to 4 kinds of `ξ` (random subset per case), `θ` factor 1 and 1.7):
```
$ python3 s1.py
random lists accepted: with order 150 | order-less with certificate (exhaustive depth<=2) 60 | of these 210, lists containing a loop / an ext-ext edge: 158 93 | rejected (no order, no cert found): 2731
  figAux: cert depth<= 0: cases 504, violations 0, max ratio 1.0000
  figAux: cert depth<= 1: cases 144, violations 0, max ratio 0.9859
  figAuxGh: cert depth<= 0: cases 72, violations 0, max ratio 0.9853
  figAux^1: cert depth 0: cases 200, violations 0, max ratio 1.0000
  figAux^1: cert depth 1: cases 48, violations 0, max ratio 0.9444
  figAux^2: cert depth 0: cases 1554, violations 0, max ratio 1.0000
  figAux^2: cert depth 1: cases 844, violations 0, max ratio 1.0000
  figAux^2: cert depth 2: cases 134, violations 0, max ratio 0.9301
  figAux^3: cert depth 0: cases 564, violations 0, max ratio 1.0000
  figAux^3: cert depth 1: cases 462, violations 0, max ratio 0.9297
  figAux^3: cert depth 2: cases 180, violations 0, max ratio 0.8946
  figAux^3: cert depth 3: cases 144, violations 0, max ratio 0.9340
  figIVext: cert depth<= 0: cases 74, violations 0, max ratio 0.3762
  random E with a nested order (OrderPin), loops/ext-ext allowed: cases 7224, violations 0, max ratio 1.0000
  random E, no order, certificate depth 1 (SumPin): cases 2752, violations 0, max ratio 1.0000
  random E, no order, certificate depth 2 (SumPin): cases 98, violations 0, max ratio 1.0000
TOTAL (E,L,psi,xi,theta,a,b) cases 14998 violations 0 max ratio 1.0
negative control E=[a0 alpha0] (no order): sum = 14.0 > theta*psi(0)^-1 = 7.5 : True
```
Union bound and `AnpDetGhAt` with `C = Π_j max(1,|P_j|)`, `c = 1/(1+Σ_j|P_j|)` at the `GhostOK` nested graphs of T2264's generator (`graphs.py gen`, seed 2270; paths through external vertices, edges on no path, ghosts at ending edges); second output line: facts for every `M` (`perPath`, `|rest|+nngh = nSolid`, `|𝓜| ≤ C`, literal `sumCertPin` certificate):
```
$ python3 s2.py
generated nested graphs 1560 | GhostOK 1363 | with >=1 ghost edge 1246 | with a ghost-free path 1124 | with a ghost path and a ghost-free path 994 | q dist {0: 0, 1: 1042, 2: 262, 3: 59, 4: 0, 5: 0} | p dist {0: 0, 1: 0, 2: 280, 3: 760, 4: 319, 5: 4}
graphs checked 1363 | reserved sets M total 7599 | |F|>C: 0 | perPath fails: 0 | |rest|+nngh!=nSolid: 0 | no literal certificate (sumCertPin) : 0 | max |F|/C = 1.000
evaluated numerically (q<=3, |F|<=40, <=12 edges): 1326 graphs
  val <= sum_M prod psi(c r) sum_l prod rest   (UnionPin): cases 46334, violations 0, max ratio 1.0000
  val <= C theta^q psi(0)^(ordN-nngh) prod psi(c r)  (AnpDetGhAt): cases 64342, violations 0, max ratio 0.2500
  sum_l prod rest(M) <= theta^q psi(0)^(|rest|-2q)  (SumPin at the actual rests): cases 317690, violations 0, max ratio 1.0000
  NEGATIVE control: c replaced by 2: cases 52754, violations 292, max ratio 38.0168
  NEGATIVE control: long-edge factors dropped: cases 52754, violations 1, max ratio 1.3334
  NEGATIVE control: theta^(q-1) in place of theta^q: cases 64342, violations 285, max ratio 4.1016
$ python3 s4.py
GhostOK nested graphs: 1363 | min over graphs of ordN-nngh: 0 | |rest|-2q == ordN-nngh for every M: True (assert)
certificate depth by (q,depth): {(1, 0): 4622, (2, 0): 1960, (2, 1): 29, (3, 0): 967, (3, 1): 21} | depth > floor(q/2) cases: 0
```
No external hypothesis occurs in the eleven targets (the merged pins carry `LWXi`, `STFlow`, `LWPsiAll` unchanged, no new one), so no limit computation is owed.

By inspection (statements read in `AnpKey.lean:30-70,689,814,825`, `AnpKey2.lean:151-191,1891`, `AnpKey5.lean:86-107`, `LWPins.lean:372-409`):
1. Order sums: the sum over `σ[m]` sees `≥ 2` list positions whose other end is external or `σ[m'], m' < m` (labels fixed), by `anpKey3_sum_xx` (`e₁ = e₂` allowed: `Σ_x ξ(y,x)² ≤ θ`); other edges at `σ[m]` (more early edges, loops: `|0| = 0`) are `≤ ψ(0)`; edges to later vertices were consumed at the later end; external-external edges `≤ ψ(0)`. Exponent `|E|-2q` in `ℤ`, `≥ 0` by the count in the table; `ψ(0) > 0`, so `zpow` is harmless.
2. Union: every path is nonempty (`WalkOK`, `a_j ≠ b_j`); `M_f` solid, `|M_f| = nngh` (edge-disjoint, nodup per path); `perPath`: a ghost-free path holds only its chosen edge (other paths' edges are disjoint), a ghost path holds `≤ 1` ghost (`GhostOK` first clause) and no `M_f` edge; the term of `ℓ` is `Π_{M_f} ξ · Π_{rest} ξ ≤ Π_j ψ(c r_j) Π_{rest} ξ` (all factors `≥ 0`), `≤` the sum over `𝓜`; `Finset.sum_comm`.
3. `anpKey5_cert` needs `IsNested` and `perPath` only; `AnpDetGhAt` follows from union + sum (`ordN = nSolid-2q`, `ordN-nngh = |rest|-2q`) with `Σ_{M∈𝓜} ≤ |𝓜|·max ≤ C·max`. Cases: `anpDetGhCaseIV_holds`, `anpDetGhStep_holds`, `anpIH_holds` follow from `anpDetGh_holds` (same `C, c`; `valOn region ≤ val`, terms `≥ 0`; case/IH hypotheses unused); `anpDetGhRegStep_holds` from `anpDetGhRegStep_of_cases` with the merged CaseI/CaseIII `_holds`.
4. Reductions: `lwAnpKeyGh_of_det : ∀ d, AnpDetGh d → LWAnpKeyGh d`, `lwAnpKey_of_gh : ∀ d, LWAnpKeyGh d → LWAnpKey d`, `lwAnp_of_key : ∀ d, LWAnpKey d → LWAnp d`: no other hypothesis, so the three `_holds` are unconditional.
5. Registry (`scanPremises`, `Axioms.lean:448-483`: a premise is dropped from the scan when some theorem has it as conclusion head): after the targets, `LWAnpKey, LWAnpKeyGh, LWAnp, AnpDetGhStep, AnpDetGhCaseI, AnpDetGhCaseIII, AnpDetGhCaseIV, AnpIH` (`:161-168`, 8 lines) are concluded by theorems (`anpDetGhCaseI_holds`, `anpDetGhCaseIII_holds` merged); no new unproved premise appears (the targets' binders are `NGraph`, `AntitoneOn`, reals), `LWXi` stays; nothing to `supersededProps`. A leftover owed line is reported as `carry nothing yet` (`:596-603`), not an error; the registry pre-check of 1b confirms.
6. §29: (1) no time variable; (2) no `1 - ilambda²/L²`; (3) no `L^d ≤ W^K`; (4) no `∀ᶠ n` in the new statements; (5) `C, c` depend on `Γ` only, quantified before `L, ψ, θ, ξ, a, b` (`AnpDetGhAt`); (6) no lower bound on `d`, `L`; (7) no scale.

### Verdicts
- `anpKey6_order` (`AnpKey6OrderPin`): PASS. `anpKey6_sum` (`AnpKey6SumPin`): PASS. `anpKey6_union` (`AnpKey6UnionPin`): PASS (7599 reserved sets, 0 failures; negative controls `c = 2`, `θ^{q-1}`, dropped long-edge factor each exceed the bound).
- `anpDetGh_holds`, `anpDetGhCaseIV_holds`, `anpDetGhStep_holds`, `anpIH_holds`, `anpDetGhRegStep_holds`, `lwAnpKeyGh_holds`, `lwAnpKey_holds`, `lwAnp_holds`: PASS (instance above; inspection 3-4).
- No counterexample to any of the three new pins; no stop condition of the ticket triggered.

## (b) Script output — Tue Oct  6 09:00:43 UTC 2026
Branch `t/T2270`, worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2270`, scratch `<scratchpad>/T2270/` (`stmt.py clash.py precheck.lean conf.lean shapes.lean ax.lean`).
```
$ git log -1 --format="%h %s"; git status --short | head -3; wc -l RBM3D/Graph/AnpKey6.lean
a9fee57 T2270: instance anpKey6_inst_apply (case IV, step, step on regions at concrete graphs)
    1136 RBM3D/Graph/AnpKey6.lean
$ lake build RBM3D.Graph.AnpKey6 RBM3D.Test.Axioms 2>&1 | grep -c "AnpKey6.lean:"   # warnings/errors in the new file; then the tail
0

Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3352 jobs).
$ grep -cE "sorry|admit|native_decide|^ *axiom " RBM3D/Graph/AnpKey6.lean   # count
0
# full build: plain `lake build` (no root import of AnpKey6, hub step) then with the root import added temporarily (plain build 09:00:23-09:00:33 UTC, with the import 08:59:25-09:00:16 UTC; saved tool logs); RBM3D.lean restored (git status: only the two files)
$ plain `lake build` (saved): the audit message and tail
3230:error: RBM3D.lean:314:0: axiom audit: 2 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `struc
  [RBM.Graph.AnpDetGhCaseIV, RBM.Graph.AnpIH]
error: build failed
lake build  7.26s user 4.97s system 119% cpu 10.233 total
$ lake build   # with `import RBM3D.Graph.AnpKey6` after the last import line of RBM3D.lean (saved tool log)
 RBM.Gauss.Sizes.STOeqNQ'].
non-vacuity certificates: 0 of 149 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4078 jobs).
```
Axioms (`lake env lean ax.lean`, `#print axioms` of all 52 public declarations; exit 0):
```
# 11 targets and 11 instance theorems: every one has axioms [propext, Classical.choice, Quot.sound]:
anpKey6_order anpKey6_sum anpKey6_union anpDetGh_holds anpDetGhCaseIV_holds anpDetGhStep_holds anpIH_holds anpDetGhRegStep_holds lwAnpKeyGh_holds lwAnpKey_holds lwAnp_holds anpKey6_inst_data anpKey6_inst_eval anpKey6_inst_det anpKey6_inst_det_eval anpKey6_inst_lw anpKey6_inst_anp anpKey6_inst_cases anpKey6_inst_apply anpKey6_inst_sum anpKey6_inst_order anpKey6_inst_union
# not standard-full: anpKey6_not_mem_take [propext, Quot.sound], anpKey6_solid_of_noGhostPath [propext, Quot.sound], anpKey6_len_le_one [propext, Quot.sound]   (subsets of the standard three)
# totals: 52 declarations, 49 with all three standard axioms; sorryAx: 0
```

Target statements, extracted from the file by `stmt.py` (finds `theorem|def <name>`, joins the lines up to the first `:=`, squeezes blanks):
```
$ python3 $S/stmt.py anpKey6_order anpKey6_sum anpKey6_union anpDetGh_holds anpDetGhCaseIV_holds anpDetGhStep_holds anpIH_holds anpDetGhRegStep_holds lwAnpKeyGh_holds lwAnpKey_holds lwAnp_holds
L481: theorem anpKey6_order : ∀ (d p q : ℕ) (E : List (NV p q × NV p q)) (σ : List (Fin q)), AnpSumOrder E σ → ∀ (L : ℕ) [NeZero L] (ψ : ℝ → ℝ) (θ : ℝ), AntitoneOn ψ (Set.Ici 0) → (∀ r : ℝ, 0 ≤ r → 0 < ψ r) → 0 < θ → ∀ ξ : Zd d L → Zd d L → ℝ, (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) → (∀ α β, ξ α β ≤ ψ ((zdistInf d L (α - β) : ℕ) : ℝ)) → (∀ α, ∑ β, ξ α β ^ 2 ≤ θ) → ∀ a b : Fin p → Zd d L, ∑ ℓ : Fin q → Zd d L, (E.map fun e => ξ (Sum.elim (Sum.elim a b) ℓ e.1) (Sum.elim (Sum.elim a b) ℓ e.2)).prod ≤ θ ^ q * ψ 0 ^ ((E.length : ℤ) - 2 * (q : ℤ))
L498: theorem anpKey6_sum : ∀ (d p q n : ℕ) (E : List (NV p q × NV p q)), AnpSumCert n E → ∀ (L : ℕ) [NeZero L] (ψ : ℝ → ℝ) (θ : ℝ), AntitoneOn ψ (Set.Ici 0) → (∀ r : ℝ, 0 ≤ r → 0 < ψ r) → 0 < θ → ∀ ξ : Zd d L → Zd d L → ℝ, (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) → (∀ α β, ξ α β ≤ ψ ((zdistInf d L (α - β) : ℕ) : ℝ)) → (∀ α, ∑ β, ξ α β ^ 2 ≤ θ) → ∀ a b : Fin p → Zd d L, ∑ ℓ : Fin q → Zd d L, (E.map fun e => ξ (Sum.elim (Sum.elim a b) ℓ e.1) (Sum.elim (Sum.elim a b) ℓ e.2)).prod ≤ θ ^ q * ψ 0 ^ ((E.length : ℤ) - 2 * (q : ℤ))
L779: theorem anpKey6_union : ∀ (p q : ℕ) (Γ : NGraph p q), Γ.GhostOK → Γ.IsNested → ∃ 𝓜 : Finset (Finset (Fin Γ.es.length)), (𝓜.card : ℝ) ≤ ∏ j, max (1 : ℝ) ((Γ.path j).length : ℝ) ∧ (∀ M ∈ 𝓜, anpKey5_perPath Γ M ∧ (anpKey5_rest Γ M).length + Γ.nngh = Γ.nSolid) ∧ ∀ (d L : ℕ) [NeZero L] (ψ : ℝ → ℝ), AntitoneOn ψ (Set.Ici 0) → (∀ r : ℝ, 0 ≤ r → 0 < ψ r) → ∀ ξ : Zd d L → Zd d L → ℝ, (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) → (∀ α β, ξ α β ≤ ψ ((zdistInf d L (α - β) : ℕ) : ℝ)) → ∀ a b : Fin p → Zd d L, Γ.val ξ a b ≤ ∑ M ∈ 𝓜, (∏ i, (if Γ.noGhostPath i = true then ψ ((1 + ∑ j, ((Γ.path j).length : ℝ))⁻¹ * ((zdistInf d L (a i - b i) : ℕ) : ℝ)) else 1)) * ∑ ℓ : Fin q → Zd d L, ((anpKey5_rest Γ M).map fun e => ξ (Sum.elim (Sum.elim a b) ℓ e.1) (Sum.elim (Sum.elim a b) ℓ e.2)).prod
L862: theorem anpDetGh_holds : ∀ d : ℕ, AnpDetGh d
L924: theorem anpDetGhCaseIV_holds : ∀ d : ℕ, AnpDetGhCaseIV d
L932: theorem anpDetGhStep_holds : ∀ d : ℕ, AnpDetGhStep d
L936: theorem anpIH_holds : ∀ d q : ℕ, AnpIH d q
L941: theorem anpDetGhRegStep_holds : ∀ d : ℕ, AnpDetGhRegStep d
L946: theorem lwAnpKeyGh_holds : ∀ d : ℕ, LWAnpKeyGh d
L949: theorem lwAnpKey_holds : ∀ d : ℕ, LWAnpKey d
L952: theorem lwAnp_holds : ∀ d : ℕ, LWAnp d
```
The compiled nonempty instances (same file, Section 6), same script (the `open ... in` of `anpKey6_inst_anp` is on the line before its `theorem`):
```
$ python3 $S/stmt.py anpKey6_inst_data anpKey6_inst_eval anpKey6_inst_det anpKey6_inst_det_eval anpKey6_inst_lw anpKey6_inst_anp anpKey6_inst_cases anpKey6_inst_apply anpKey6_inst_sum anpKey6_inst_order anpKey6_inst_union
L969: theorem anpKey6_inst_data : AntitoneOn (fun r : ℝ => (1 + r)⁻¹) (Set.Ici 0) ∧ (∀ r : ℝ, 0 ≤ r → 0 < (fun r : ℝ => (1 + r)⁻¹) r) ∧ (0 : ℝ) < 1 ∧ (∀ _α _β : Zd 3 3, (0 : ℝ) ≤ 1 / 6 ∧ (1 / 6 : ℝ) = 1 / 6) ∧ (∀ α β : Zd 3 3, (1 / 6 : ℝ) ≤ (fun r : ℝ => (1 + r)⁻¹) ((zdistInf 3 3 (α - β) : ℕ) : ℝ)) ∧ (∀ _α : Zd 3 3, ∑ _β : Zd 3 3, (1 / 6 : ℝ) ^ 2 ≤ 1)
L993: theorem anpKey6_inst_eval {p q : ℕ} (Γ : NGraph p q) (hG : Γ.GhostOK) (hN : Γ.IsNested) : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ c ≤ 1 ∧ Γ.val (fun _ _ : Zd 3 3 => (1 / 6 : ℝ)) (fun _ => (0 : Zd 3 3)) (fun _ => (1 : Zd 3 3)) ≤ C * (1 : ℝ) ^ q * (fun r : ℝ => (1 + r)⁻¹) 0 ^ (Γ.ordN - (Γ.nngh : ℤ)) * ∏ i, (if Γ.noGhostPath i = true then (fun r : ℝ => (1 + r)⁻¹) (c * ((zdistInf 3 3 ((fun _ => (0 : Zd 3 3)) i - (fun _ => (1 : Zd 3 3)) i) : ℕ) : ℝ)) else 1)
L1005: theorem anpKey6_inst_det : AnpDetGhAt 3 figAux ∧ AnpDetGhAt 3 anpKey5_figIVext ∧ AnpDetGhAt 3 anpKey2_figAuxGh
L1012: theorem anpKey6_inst_det_eval : (∃ C c : ℝ, 0 < C ∧ 0 < c ∧ c ≤ 1 ∧ figAux.val (fun _ _ : Zd 3 3 => (1 / 6 : ℝ)) (fun _ => (0 : Zd 3 3)) (fun _ => (1 : Zd 3 3)) ≤ C * (1 : ℝ) ^ 2 * (fun r : ℝ => (1 + r)⁻¹) 0 ^ (figAux.ordN - (figAux.nngh : ℤ)) * ∏ i, (if figAux.noGhostPath i = true then (fun r : ℝ => (1 + r)⁻¹) (c * ((zdistInf 3 3 ((fun _ => (0 : Zd 3 3)) i - (fun _ => (1 : Zd 3 3)) i) : ℕ) : ℝ)) else 1)) ∧ (∃ C c : ℝ, 0 < C ∧ 0 < c ∧ c ≤ 1 ∧ anpKey5_figIVext.val (fun _ _ : Zd 3 3 => (1 / 6 : ℝ)) (fun _ => (0 : Zd 3 3)) (fun _ => (1 : Zd 3 3)) ≤ C * (1 : ℝ) ^ 1 * (fun r : ℝ => (1 + r)⁻¹) 0 ^ (anpKey5_figIVext.ordN - (anpKey5_figIVext.nngh : ℤ)) * ∏ i, (if anpKey5_figIVext.noGhostPath i = true then (fun r : ℝ => (1 + r)⁻¹) (c * ((zdistInf 3 3 ((fun _ => (0 : Zd 3 3)) i - (fun _ => (1 : Zd 3 3)) i) : ℕ) : ℝ)) else 1)) ∧ (∃ C c : ℝ, 0 < C ∧ 0 < c ∧ c ≤ 1 ∧ anpKey2_figAuxGh.val (fun _ _ : Zd 3 3 => (1 / 6 : ℝ)) (fun _ => (0 : Zd 3 3)) (fun _ => (1 : Zd 3 3)) ≤ C * (1 : ℝ) ^ 2 * (fun r : ℝ => (1 + r)⁻¹) 0 ^ (anpKey2_figAuxGh.ordN - (anpKey2_figAuxGh.nngh : ℤ)) * ∏ i, (if anpKey2_figAuxGh.noGhostPath i = true then (fun r : ℝ => (1 + r)⁻¹) (c * ((zdistInf 3 3 ((fun _ => (0 : Zd 3 3)) i - (fun _ => (1 : Zd 3 3)) i) : ℕ) : ℝ)) else 1))
L1037: theorem anpKey6_inst_lw : LWAnpKeyGh 3 ∧ LWAnpKey 3 ∧ LWAnp 3
L1043: theorem anpKey6_inst_anp (ξ : ∀ n, Zd 3 (sz0.L n) → Zd 3 (sz0.L n) → sz0.SeqΩ → ℝ) (hξ : LWXi sz0 (STflowE z0) tInst Φ0 ξ) : (∃ c : ℝ, 0 < c ∧ Prec sz0 (U
L1061: theorem anpKey6_inst_cases : AnpDetGhCaseI 3 ∧ AnpDetGhCaseIII 3 ∧ AnpDetGhCaseIV 3 ∧ AnpDetGhRegStep 3 ∧ AnpDetGhStep 3 ∧ AnpIH 3 2 ∧ LWAnpKeyGh 3 ∧ LWAnpKeyGh 3
L1073: theorem anpKey6_inst_apply : AnpDetGhRegAt 3 anpKey5_figIVext anpKey5_piIV ∧ AnpDetGhAt 3 figAux ∧ AnpDetGhRegAt 3 anpKey2_figAuxGh (fun _ _ => false)
L1086: theorem anpKey6_inst_sum : ∑ ℓ : Fin 2 → Zd 3 3, ((anpKey5_rest figAux anpKey5_resAux).map fun e : NV 2 2 × NV 2 2 => (fun _ _ : Zd 3 3 => (1 / 6 : ℝ)) (Sum.elim (Sum.elim (fun _ : Fin 2 => (0 : Zd 3 3)) (fun _ : Fin 2 => (1 : Zd 3 3))) ℓ e.1) (Sum.elim (Sum.elim (fun _ : Fin 2 => (0 : Zd 3 3)) (fun _ : Fin 2 => (1 : Zd 3 3))) ℓ e.2)).prod ≤ (1 : ℝ) ^ 2 * (fun r : ℝ => (1 + r)⁻¹) 0 ^ (((anpKey5_rest figAux anpKey5_resAux).length : ℤ) - 2 * (2 : ℤ))
L1100: theorem anpKey6_inst_order : ∑ ℓ : Fin 1 → Zd 3 3, ((anpKey5_rest anpKey5_figIVext ∅).map fun e : NV 2 1 × NV 2 1 => (fun _ _ : Zd 3 3 => (1 / 6 : ℝ)) (Sum.elim (Sum.elim (fun _ : Fin 2 => (0 : Zd 3 3)) (fun _ : Fin 2 => (1 : Zd 3 3))) ℓ e.1) (Sum.elim (Sum.elim (fun _ : Fin 2 => (0 : Zd 3 3)) (fun _ : Fin 2 => (1 : Zd 3 3))) ℓ e.2)).prod ≤ (1 : ℝ) ^ 1 * (fun r : ℝ => (1 + r)⁻¹) 0 ^ (((anpKey5_rest anpKey5_figIVext ∅).length : ℤ) - 2 * (1 : ℤ))
L1114: theorem anpKey6_inst_union : ∃ 𝓜 : Finset (Finset (Fin figAux.es.length)), (𝓜.card : ℝ) ≤ 9 ∧ (∀ M ∈ 𝓜, anpKey5_perPath figAux M ∧ (anpKey5_rest figAux M).length + figAux.nngh = figAux.nSolid) ∧ figAux.val (fun _ _ : Zd 3 3 => (1 / 6 : ℝ)) (fun _ => (0 : Zd 3 3)) (fun _ => (1 : Zd 3 3)) ≤ ∑ M ∈ 𝓜, (∏ i, (if figAux.noGhostPath i = true then (fun r : ℝ => (1 + r)⁻¹) ((1 + ∑ j, ((figAux.path j).length : ℝ))⁻¹ * ((zdistInf 3 3 ((fun _ => (0 : Zd 3 3)) i - (fun _ => (1 : Zd 3 3)) i) : ℕ) : ℝ)) else 1)) * ∑ ℓ : Fin 2 → Zd 3 3, ((anpKey5_rest figAux M).map fun e : NV 2 2 × NV 2 2 => (fun _ _ : Zd 3 3 => (1 / 6 : ℝ)) (Sum.elim (Sum.elim (fun _ : Fin 2 => (0 : Zd 3 3)) (fun _ : Fin 2 => (1 : Zd 3 3))) ℓ e.1) (Sum.elim (Sum.elim (fun _ : Fin 2 => (0 : Zd 3 3)) (fun _ : Fin 2 => (1 : Zd 3 3))) ℓ e.2)).prod
```
Pins and shapes (`conf.lean` = check-file section 2 lines 132-214 + T2264 check lines 98-246 verbatim + `audit_sumCert_iff` of T2264 audit §1 + the `example`s below; `shapes.lean` = the five check-file section-3 shapes, each closed by the instance):
```
$ lake env lean conf.lean; echo exit=$?
exit=0
$ grep -c "^example" conf.lean; grep "^example" conf.lean | <names>   # 19 = 4 `example : Prop` shapes of T2264 section 3, the 11 pins of T2270 section 2, and 4 T2264 interface checks (`@sumOrderPin = @AnpSumOrder`, `AnpKey6SumPin`, `AnpKey6DirectPin`, `AnpKey6IVPin`)
19
Prop Prop Prop Prop AnpKey6OrderPin AnpKey6SumPin AnpKey6UnionPin AnpKey6DirectPin AnpKey6IVPin AnpKey6StepPin AnpKey6IHPin AnpKey6RegStepPin AnpKey6KeyGhPin AnpKey6KeyPin AnpKey6AnpPin @sumOrderPin AnpKey6SumPin AnpKey6DirectPin AnpKey6IVPin 
$ lake env lean shapes.lean; echo exit=$?
exit=0
```
Registry (`Test/Axioms.lean`): the diff against `main` and the pre-check (`precheck.lean` = `import RBM3D`, `import RBM3D.Graph.AnpKey6`, `import RBM3D.Test.Axioms`, `#assert_rbm_axioms`, after `lake build RBM3D.Test.Axioms`):
```
$ git diff main...t/T2270 --stat; ... -- Axioms.lean: count of +/- lines; the names on the deleted lines
 RBM3D/Graph/AnpKey6.lean | 1136 ++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean   |    8 -
 2 files changed, 1136 insertions(+), 8 deletions(-)
   8 - 
RBM.Gauss.Sizes.LWAnpKey RBM.Gauss.Sizes.LWAnpKeyGh RBM.Gauss.Sizes.LWAnp RBM.Graph.AnpDetGhStep RBM.Graph.AnpDetGhCaseI RBM.Graph.AnpDetGhCaseIII RBM.Graph.AnpDetGhCaseIV RBM.Graph.AnpIH 
$ lake env lean precheck.lean; echo exit=$?   # started Tue Oct  6 08:58:30 UTC 2026, done Tue Oct  6 08:59:21 UTC 2026 (UTC)
exit=0
$ head -1 precheck.out; grep "^premises found\|^registry:" precheck.out | cut -c1-200
axiom audit: 7937 theorems, 2612 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
156:premises found by scanning: 151 (borrowed 1, owed 93, structural 40, refuted 6, superseded 11).
157:registry: 2 borrowed + 147 owed + 103 structural + 7 refuted + 12 superseded; 120 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
$ for each of the 8 deleted names: grep -c "<name>([,:]|])" precheck.out   # entries in the ledger text
RBM.Gauss.Sizes.LWAnpKey: 0 RBM.Gauss.Sizes.LWAnpKeyGh: 0 RBM.Gauss.Sizes.LWAnp: 0 RBM.Graph.AnpDetGhStep: 0 RBM.Graph.AnpDetGhCaseI: 0 RBM.Graph.AnpDetGhCaseIII: 0 RBM.Graph.AnpDetGhCaseIV: 0 RBM.Graph.AnpIH: 0 
```
Name clash and ports:
```
$ python3 clash.py   # grep -rnw <each new name> RBM3D --include=*.lean (outside AnpKey6.lean) and docs/tickets/T2271.md
new declarations: 54; hits in other RBM3D/*.lean files: 0; hits in docs/tickets/T2271.md: 0
$ grep -rnE "NGraph|IsNested|AnpDetGh|NEdge" ../RBM1D ../RBM2D --include=*.lean | grep -v /.lake/ | wc -l   # no light-weight graph layer: no port, no diff-stat
       0
```
Every public declaration with its line (script: `grep -nE "^(private )?(theorem|def) "`; 54 declarations, 2 private):
```
anpKey6_F:55 anpKey6_prod_eq:59 anpKey6_Em:66 anpKey6_early_succ:70 anpKey6_early_mono:78 anpKey6_not_mem_take:82 anpKey6_lab_update:92 anpKey6_peel:102 anpKey6_A_mem:130 anpKey6_A_val:150 anpKey6_order_step:170
anpKey6_order_gen:301 anpKey6_prod_set_mul:378 anpKey6_amgm:394 anpKey6_sum_gen:431 anpKey6_le_psi0:474 anpKey6_order:481 anpKey6_sum:498 anpKey6_M:523 anpKey6_solid_of_noGhostPath:527 anpKey6_choice_inj:533 anpKey6_M_card:539
anpKey6_len_le_one:545 anpKey6_perPath:555 anpKey6_nSolid_card:595 anpKey6_rest_length:603 anpKey6_rest_prod:626 anpKey6_w:664 anpKey6_val_eq:669 anpKey6_w_nonneg:676 anpKey6_point:686 anpKey6_union:779 anpDetGh_holds:862
anpKey6_valOn_le:910 anpDetGhCaseIV_holds:924 anpDetGhStep_holds:932 anpIH_holds:936 anpDetGhRegStep_holds:941 lwAnpKeyGh_holds:946 lwAnpKey_holds:949 lwAnp_holds:952 anpKey6_zdist_three_le*:960 anpKey6_zdistInf_three_le*:964
anpKey6_inst_data:969 anpKey6_inst_eval:993 anpKey6_inst_det:1005 anpKey6_inst_det_eval:1012 anpKey6_inst_lw:1037 anpKey6_inst_anp:1043 anpKey6_inst_cases:1061 anpKey6_inst_apply:1073 anpKey6_inst_sum:1086 anpKey6_inst_order:1100
anpKey6_inst_union:1114
```

### Narrative (script output above is the evidence)
- Section (a) is not edited and no (a′) is needed; the three new pins and the eleven targets are stated exactly as the check file (`conf.lean`, exit 0). The file has 1136 lines (ticket's stop threshold: 1500).
- Route as the ticket (`DECISIONS §87 (2)`): one union bound over the long edges of the ghost-free paths (`anpKey6_union`), the merged certificate (`anpKey5_cert`), the sums along it (`anpKey6_sum`); no induction on `q`, no region, no case. The case, induction and `k < q` hypotheses of `anpDetGhCaseIV_holds`, `anpDetGhStep_holds`, `anpIH_holds` are `_` binders (unused).
- Section 1: `anpKey6_order_step` is the step `m+1 → m` of a downward induction on the prefix length of `σ`; `anpKey6_peel` splits off the coordinate `σ[m]`; two counted positions of `AnpSumOrder` (`anpKey6_A_mem`, `anpKey6_A_val`) give `Σ_x ξ(x,y₁) ξ(x,y₂) ≤ θ` by the merged `anpKey3_sum_xx`, the other edges of the prefix `m+1` are `≤ ψ(0)`.  With integer (`zpow`) exponents the exponent identity is linear arithmetic (`omega`), so the ticket's count `N_m ≥ 2(q-m)` is not needed.  `anpKey6_order_gen` is for a general finite label set (`ξ ≥ 0` symmetric, `ξ ≤ ψ₀`, row sums `≤ θ`); the pin is its wrapper with `ψ₀ = ψ 0`.
- Section 2: `anpKey6_prod_set_mul` (`(l.set j a).prod * l[j] = l.prod * a`) gives `anpKey6_amgm` pointwise (`2 P ≤ P₁ + P₂`); both leaf lists have the length of `E` (`List.length_set`), so the induction on the depth gives `Σ ≤ ½(B + B) = B`.
- Section 3: `anpKey6_M` is the reserved set of a choice function; `anpKey6_perPath` (edge-disjoint paths with duplicate-free edge lists, `GhostOK` first clause), `anpKey6_rest_length` (`|rest| + n_ngh = n_S`), `anpKey6_point` (one labelling: choice by `anpKey_long_edge`, each factor is `[k ∈ M] w_k · [solid, k ∉ M] ξ_k`, `c r_j ≤ len` from `r_j ≤ |𝔓_j| len`), `anpKey6_union` (the family is the image of the choice functions; sum over labellings exchanged with the sum over the family).
- Section 4: `anpDetGh_holds` with `C = Π_j max 1 |𝔓_j|`, `c = (1 + Σ_j |𝔓_j|)⁻¹` as in the ticket; `(|rest| : ℤ) - 2q = ordN - n_ngh` by `omega` from `|rest| + n_ngh = n_S`.  Section 5: `anpKey6_valOn_le` (subset of `univ`, terms `≥ 0`) and one-line corollaries; `anpDetGhRegStep_holds` uses the merged `anpDetGhCaseI_holds`, `anpDetGhCaseIII_holds`.
- Registry: the eight lines are deleted, none added (pre-check exit 0, the eight names have 0 entries in the ledger text).  The plain `lake build` of the branch fails at `#assert_rbm_axioms` with the unregistered premises `[AnpDetGhCaseIV, AnpIH]`, because the theorems that prove them live in `AnpKey6`, not yet imported by `RBM3D.lean` (the hub adds the import at merge, CLAUDE.md §3 (A) 4).  With the import added temporarily to `RBM3D.lean` (restored from a copy afterwards) `lake build` exits 0.
- Instances (Section 6): `anpKey6_inst_data` discharges every deterministic hypothesis at `d = L = 3`, `ψ r = (1+r)⁻¹`, `θ = 1`, `ξ ≡ 1/6`; `anpKey6_inst_eval`/`_det_eval` put the bound at `figAux`, `anpKey5_figIVext`, `anpKey2_figAuxGh` (`a ≡ 0`, `b ≡ 1`); `_apply` applies case (IV), the step and the step on regions at `anpKey5_figIVext`, `figAux`, `anpKey2_figAuxGh` (merged instance data `anpKey5_inst_figIVext`, `anpKey2_inst_figAuxGh`); `_sum` at the depth-1 certificate (AM-GM), `_order` at the nested order `[α]` of `figIVext`, `_union` at `figAux`; `_anp` keeps only `ξ` and `LWXi` (the owed premise).  `shapes.lean` closes the five check-file shapes with them.

### (c) Verified Mathlib/core names used (all `#check @name` in `chknames.lean`: exit 0, 0 errors; all 106 occur in `AnpKey6.lean`)
```
Bool.and_eq_true Bool.false_eq_true Bool.false_or Bool.or_eq_true Fin.prod_univ_def Fin.prod_univ_two Finset.card_filter Finset.card_image_le Finset.card_image_of_injective Finset.card_pair
Finset.card_sdiff_add_card_eq_card Finset.card_univ Finset.mem_filter Finset.mem_image Finset.mem_insert Finset.mem_sdiff Finset.mem_singleton Finset.mem_univ Finset.mul_sum Finset.one_lt_card
Finset.prod_congr Finset.prod_const Finset.prod_filter Finset.prod_image Finset.prod_ite_mem Finset.prod_le_prod₀ Finset.prod_mul_distrib Finset.prod_nonneg Finset.prod_pair Finset.prod_pos
Finset.prod_sdiff Finset.single_le_sum Finset.subset_univ Finset.sum_add_distrib Finset.sum_comm Finset.sum_congr Finset.sum_const Finset.sum_const_zero Finset.sum_ite_eq Finset.sum_ite_eq'
Finset.sum_le_sum Finset.sum_le_sum_of_subset_of_nonneg Finset.sum_nonneg Finset.sup_le Finset.univ Finset.univ_inter Fintype.card_piFinset Fintype.mem_piFinset Fintype.piFinset Function.Injective
Function.update Function.update_of_ne List.Nodup.sublist List.all_eq_true List.countP_eq_length_filter List.countP_true List.eq_replicate_iff List.filterMap_cons List.filter_congr List.filter_sublist
List.getElem_cons_succ List.getElem_cons_zero List.getElem_mem List.get_eq_getElem List.get_mem List.length_set List.map_cons List.map_set List.mem_append List.mem_filter List.mem_iff_get List.mem_map
List.mem_or_eq_of_mem_set List.mem_singleton List.mem_take_iff_getElem List.nodup_replicate List.not_mem_nil List.ofFn_getElem_eq_map List.prod_cons List.prod_eq_zero List.prod_nonneg List.prod_ofFn
List.set_cons_succ List.set_cons_zero List.take_add_one List.take_of_length_le List.take_zero List.toFinset_card_of_nodup Nat.cast_nonneg Option.toList_some inv_anti₀ inv_le_one_of_one_le₀
inv_mul_le_iff₀ mul_le_mul_of_nonneg_left mul_le_mul_of_nonneg_right mul_nonneg mul_pos nonneg_of_mul_nonneg_left nsmul_eq_mul one_div_le_one_div_of_le one_pos pow_nonneg pow_succ zpow_add₀
zpow_natCast zpow_nonneg
```
The two-argument use `Finset.prod_le_prod h0 h1` failed with "Function expected" (tool log of the first compile of `anpKey6_union`): `Finset.prod_le_prod₀` is used.  `List.take_succ` is deprecated (`#check` warning, tool log): `List.take_add_one` is used.  Names verified absent: none looked for.

### (d) Open issues and paper-delta candidates
- Open: `LWXi` stays owed at its registry line (`anpKey6_inst_anp` takes `ξ`, `hξ : LWXi …`).  The hub must add `import RBM3D.Graph.AnpKey6` to `RBM3D.lean` at merge; without it the plain `lake build` fails as shown above.  The sibling ticket T2265 moves `LWG5Expand` (`Axioms.lean:158`) and this branch deletes `:161-168` (diff hunk `@@ -158,14 +158,6 @@`): both anchor by text.
- `AnpKey3`/`AnpKey4` (cases (I)-(III), merged) are proved theorems that this route does not use for `LWAnpKeyGh`; their pins are closed by `anpDetGhCaseI_holds`, `anpDetGhCaseIII_holds` (merged) and `anpDetGhCaseIV_holds` (here).
- `T2270a`: `lem:Anp_key_gh` (`7_8:1041-1077`) is proved without the induction on `q` and without regions or cases (`7_8:1105-1384`): one union bound over the long edges of the ghost-free paths (the argument of `7_8:1110`), the summation certificate of T2264 and the sums along it.
- `T2270b`: explicit constants `C = Π_j max(1, |𝔓_j|)`, `c = 1/(1 + Σ_j |𝔓_j|)`; the paper's `c` comes out of the induction.
- `T2270c`: the AM-GM re-rooting (`7_8:1428-1451`) is a finite binary tree of splits, each with weights `½ + ½` (`anpKey6_amgm`, `anpKey6_sum_gen`); Lean has `∃ n` (`anpKey5_cert`), the depth bound `⌊q/2⌋` is not a Lean statement (preflight (a) tested it at 1363 graphs, 0 violations).
- §29 checklist: as (a) inspection 6; the new statements have no time variable, no `∀ᶠ`, `C, c` depend on `Γ` only and are quantified before `L, ψ, θ, ξ, a, b`, any `d` and `L ≥ 1` (`[NeZero L]`).
