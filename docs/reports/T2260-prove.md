Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 06:05 UTC 2026

### (i) Exponent table (`Γ` has `q = q'+1` internal vertices; `Γ'' := anpKey3_gh2 (anpKey2_fixV Γ i₀ s₀) (em m₁) (em m₂)`)

| Quantity | Value | Constraint | Slack |
|---|---|---|---|
| IH index | `Γ'' : NGraph p'' q'`, `k = q-1` | `AnpIH d q` needs `k < q` (any `p''`, any number of edges) | 1 |
| `p''` | `p+2`: `j₁,j₂` visit `α` once each (ghost `k_t` and solid `m_t` at `α`, so 2 segments each); any other path visiting `α` has a solid edge at `α` (ghost edges are ending edges, a walk continues through `α`), which would be `m₁` or `m₂` | none needed by Lean; script asserts `p''=p+2` | — |
| `nSolid''` | `nSolid - 2` (F8: `nSolid' = nSolid`; gh2: `nSolid'' + 2 = nSolid'`) | `m₁ ≠ m₂` solid (`IsNested` conj. 4, `j₁ ≠ j₂`) | exact |
| `ordN''` | `nSolid'' - 2q' = ordN` (`ord = nS + 2(nW - nV)`, `nW = 0`, `nV = q`) | `(nSolid-2) - 2(q-1) = nSolid - 2q` | exact (`omega`) |
| `nngh''` | `= nngh`: `r_t = [em k_t]` and `r'_t` (made ghost) are the only two segments of `j_t`; every other path is one segment | `anpKey3_prod` needs only `nngh'' ≥ nngh` (`ρ` injective) | 0 in all scripts |
| `ψ(0)` exponent | `(ordN''-nngh'') + (nngh''-nngh) = ordN - nngh` | `zpow_add₀`, `ψ 0 > 0` (from `∀ r ≥ 0, 0 < ψ r`) | exact |
| `θ` exponent | `θ · θ^{q'} = θ^q` | IH gives `θ^{q'}` for `Γ''` | exact |
| `C` | the IH constant of `Γ''`, unchanged | `0 < C` | — |
| `c` | `c'' ↦ c''/2 ∈ (0, 1/2] ⊂ (0,1]` | `ψ(c''·|a''_r-b''_r|) ≤ ψ((c''/2)|a_j-b_j|)` ⇐ `|a_j-b_j| ≤ 2|a''_r-b''_r|` (`anpKey3_far_gen`, triangle inequality, `ψ` antitone on `[0,∞)`) | factor 2; for ghost-free `j` the single segment has `|a''-b''| = |a_j-b_j|`, so `c''` itself would do |
| `ψ` bound for `anpKey3_prod` | ghost-free `r`: `0 ≤ ψ(c''·dist) ≤ ψ(0)` | `c''·dist ≥ 0`, antitone | `ψ(0) - ψ(c''dist) ≥ 0` |
| factor split | `ξ(x,y₁(ℓ)) ξ(x,y₂(ℓ))`, `y_t` = label of `β_t ≠ inr i₀` (no self-loop, `IsNested` conj. 1) | `ξ` symmetric; `y_t` free of `x` (`Fin.insertNth_apply_succAbove`) | — |
| `Σ_x ξ(y₁,x)ξ(y₂,x)` | `≤ θ` (`½(Σξ(y₁,·)² + Σξ(y₂,·)²)`, `anpKey3_sum_xx`, `R = regionOne ⊆ univ`, `ξ ≥ 0`) | `Σ_β ξ_{αβ}² ≤ θ` for both rows | 0 only if both rows saturate |
| `deg_s(α) = 2` | solid edges at `α` are exactly `{m₁, m₂}` | gives: every solid edge of `Γ''` (`em k`, `k ∉ {m₁,m₂}`) avoids the `x`-copies; so `ep''` is `x`-independent | 0; with `deg_s > 2`: 5/5 test cases have a solid `Γ''`-edge at an `x`-copy (degs.py (2)) |
| used hypotheses | `ξ ≥ 0` (F3, drop region and rows `≠ π i₀`), symmetry, `Σξ² ≤ θ`; `ψ > 0`, antitone, `ξ ≤ ψ` only inside IH and the product step | `NoA2 π`, the region `𝐃_π`, `(eq:Psi)` are not used | — |

Instances of the data (from `c3.py inst`, output pasted in (ii); `i₀` = the index of `α`; `r_t` = `[em k_t]`, `r'_t` = segment of `j_t` whose head (`s_t=F`) / last step (`s_t=T`) is `em m_t`):

| | `figLoop`, `i₀=0`, `π=piLoop` | `figAuxGh`, `i₀=1` (ℳ₂), `π ≡ false` | `figLoop3` (= `figLoop` + ghost-free path 2) |
|---|---|---|---|
| `(j_t, s_t, k_t)` | `(0,F,0), (1,F,3)` | `(0,T,4), (1,T,5)` | as `figLoop` |
| `m_t`, `β_t` | `1, 4`; `β₁ = a_0 = a_{j₁}` (self-loop of the paper), `β₂ = b_1` | `2, 3`; `β₁ = β₂ = ℳ₁` | as `figLoop` |
| `p'', p` | `4, 2` | `4, 2` | `5, 3` |
| `own, ea, eb` | `[0,0,1,1]`, `[a0,·,a1,·]`, `[·,b0,·,b1]` | same | `+ own 2, ea a2, eb b2` |
| `r_t`; `r'_t` | `0, 2`; `1, 3` (heads) | `1, 3`; `0, 2` (last steps) | `0, 2`; `1, 3` |
| `nSolid''`, `ordN''`, `ordN` | `1, 1, 1` | `2, 0, 0` | `2, 2, 2` |
| `nngh''`, `nngh` | `0, 0` | `0, 0` | `1, 1` |
| `ρ j` (step 6) | vacuous (`nngh = 0`) | vacuous | `ρ(2) = 4` (`own 4 = 2`, `a2 → b2`) |
| constants | `(C'', c''/2)` | `(C'', c''/2)` | `(C'', c''/2)` |

### (ii) One concrete nondegenerate instance

`d = 3`, `L = 5` (125 sites), `Γ = figLoop`: `p = 2`, `q = 1`, `GhostOK`, `IsNested`, `NoA2 piLoop`, `¬ AnpCaseI`, `AnpCaseIII` (`degS = [2]`), `ordN = 1`, `nngh = 0`; `ψ ∈ {1/(1+r), exp(-r/2)}` (positive, antitone), `ξ = ψ(dist)·U` with `U` symmetric in `[0,1]` (so `ξ ≥ 0`, symmetric, `ξ ≤ ψ(dist)`), `θ = max_α Σ_β ξ² > 0`. Also `figAuxGh` at ℳ₂ (`L = 5`) and `figLoop3` (`L = 3`). The only premise that is another gate's pin is `AnpIH 3 1` (induction hypothesis, concerns `q = 0` graphs); its conclusion for the one graph used, `Γ'' ∈ NGraph 4 0` (one solid edge `a_0 b_0`, `ordN'' = 1`, `nngh'' = 0`), reads `ξ(a_0,b_0) ≤ C ψ(0)`, true with `(C,c) = (1,1)` (`ξ ≤ ψ(dist) ≤ ψ(0)`); script column "IH-bound at G2" (`G2` = `Γ''`) evaluates it. There is no limit or external-input hypothesis in the targets (deterministic; no `N`, no `∀ᶠ`), so no limit computation applies.

Command (Python only, scratch `<scratchpad>/T2260/`, scripts `c3.py`, `degs.py`, helpers `g.py lib*.py fix.py` copied from T2252's scratch; `bash run.sh`) and verbatim output:
```
$ python3 c3.py inst
== instance data (check file figLoop/piLoop; figAuxGh at M(1); figLoop3 = figLoop + ghost-free path 2)
figLoop: nested True ghostOK True noA2(pi=false) True caseI False caseIII True p=2 q=1 nSolid=3 ordN=1 nngh=0 degS=[2]
  i0=0 (j,s,k)=(0,False,0),(1,False,3) m=[1, 4] beta=[('a', 0), ('b', 1)] loop=[True, False] p''=4 own=[0, 0, 1, 1] ea=[('a', 0), None, ('a', 1), None] eb=[None, ('b', 0), None, ('b', 1)]
    r_t=[0, 2] r'_t=[1, 3] (head if s=F, last if s=T) nSolid''=1 ordN''=1 nngh''=0 nngh=0 ngp''=[]
figAuxGh@M1: nested True ghostOK True noA2(pi=false) True caseI True caseIII True p=2 q=2 nSolid=4 ordN=0 nngh=0 degS=[4, 2]
  i0=1 (j,s,k)=(0,True,4),(1,True,5) m=[2, 3] beta=[('m', 0), ('m', 0)] loop=[False, False] p''=4 own=[0, 0, 1, 1] ea=[('a', 0), None, ('a', 1), None] eb=[None, ('b', 0), None, ('b', 1)]
    r_t=[1, 3] r'_t=[0, 2] (head if s=F, last if s=T) nSolid''=2 ordN''=0 nngh''=0 nngh=0 ngp''=[]
figLoop3: nested True ghostOK True noA2(pi=false) True caseI False caseIII True p=3 q=1 nSolid=4 ordN=2 nngh=1 degS=[2]
  i0=0 (j,s,k)=(0,False,0),(1,False,3) m=[1, 4] beta=[('a', 0), ('b', 1)] loop=[True, False] p''=5 own=[0, 0, 1, 1, 2] ea=[('a', 0), None, ('a', 1), None, ('a', 2)] eb=[None, ('b', 0), None, ('b', 1), ('b', 2)]
    r_t=[0, 2] r'_t=[1, 3] (head if s=F, last if s=T) nSolid''=2 ordN''=2 nngh''=1 nngh=1 ngp''=[4]
$ python3 c3.py inst_num
figLoop d=3 L=5 (125 sites) i0=0: 24 (xi,a,b,pi) cases: max valOn/(theta*G''.val(x0)) = 0.5284; max per-x factorisation rel.err 2.0e-16; max x-independence rel.dev 0.0e+00; max prod-step ratio 1.0000; IH-bound at G2 (C,c)=(1,1): max ratio 0.6065; target bound (C,c/2)=(1,1/2): max ratio 0.3057
figAuxGh@M1 d=3 L=5 (125 sites) i0=1: 96 (xi,a,b,pi) cases: max valOn/(theta*G''.val(x0)) = 0.6320; max per-x factorisation rel.err 2.2e-16; max x-independence rel.dev 0.0e+00; max prod-step ratio 1.0000; IH-bound at G2 (C,c)=(1,1): max ratio 0.9576; target bound (C,c/2)=(1,1/2): max ratio 0.6052
figLoop3 d=3 L=3 (27 sites) i0=0: 96 (xi,a,b,pi) cases: max valOn/(theta*G''.val(x0)) = 0.8931; max per-x factorisation rel.err 2.4e-16; max x-independence rel.dev 0.0e+00; max prod-step ratio 0.9394; IH-bound at G2 (C,c)=(1,1): max ratio 0.6065; target bound (C,c/2)=(1,1/2): max ratio 0.4219
$ python3 c3.py rand
graphs=260 (graph,i0,pair) data=260; self-loop configs (beta_t=a_j for s=F / b_j for s=T) 143; s1!=s2: 147; beta1=beta2: 70; with off-path ghost edge at alpha: 40; pi without NoA2 among tested: 21
numeric (Z_3^3, 27 sites): 3120 (xi,a,b,pi) cases: max valOn/(theta*G''.val(x0)) = 0.9797 (<=1 needed); per-x factorisation rel.err 7.5e-16; x-independence rel.dev 0.0e+00; product-step max ratio 1.0000 (<=1 needed)
asserted for every datum: j1!=j2; m_t solid at alpha, m1!=m2, {solid at alpha}={m1,m2}; G' F1-F8; r_t one-step ghost; r'_t unique, ghost-free in G', head (s=F)/last (s=T) = m_t, r'_1!=r'_2; G'' GhostOK+nested, nSolid''+2=nSolid, ordN''=ordN, noGhost iff, transfer clause, nngh''=nngh, p''=p+2; no solid edge of G'' at an x-copy; no self-loop at the ghostified edge; far_gen(2x) at every j
$ python3 degs.py
(1) ne: 300 nested ghostOK graphs, 259 pairs of distinct B2 ending edges at one vertex (any deg_s): pairs with j1=j2: 0
(2) pairs with deg_s>2: 5; of them a solid edge of G'' still touches the x-copy (x-independence fails): 5
```
(`ratio` columns: `valOn Γ (region π) / (θ·Γ''.val x₀)` must be `≤ 1`; "per-x factorisation" checks `Γ'.val(x) = Σ_ℓ ξ(x,y₁(ℓ)) ξ(x,y₂(ℓ)) ep''(x₀,ℓ)` for random `x`; `G2` = `Γ''`; "target bound" is the conclusion of `AnpDetGhRegAt` with `(C,c/2) = (1,1/2)` at the instance.)

### Verdicts

- `anpKey4_caseIII_ne` (`AnpKey4NePin`): PASS. `j₁ = j₂` ⇒ `s₁ ≠ s₂`; head and last step both ghost; a path of length 1 is the edge `a_j b_j`, not at `α`; length `≥ 2` gives two distinct edges (`IsNested` conj. 3) contradicting `GhostOK`. Script: 259 pairs, 0 violations.
- `anpKey4_solid` (`AnpKey4SolidPin`): PASS. `anpKey2_endAt_ends` puts `k_t` at `(k_t, inr i₀)` (head) or after arrival `(m_t, inr i₀)` (last); `m_t` solid by `GhostOK`; `m₁ ≠ m₂` by edge-disjointness; `deg_s = 2` gives the last clause. Asserted in every datum.
- `anpKey4_gh2_props` (`AnpKey4Gh2Pin`): PASS (as `anpKey3_gh2_props`; the proof uses only that `st_t` is the first or last step of a ghost-free path and that edges of distinct paths differ). Asserted: `GhostOK`, `IsNested`, `nSolid''+2`, iff on `noGhostPath`, 260 data.
- `anpKey4_reduce` (`AnpKey4ReducePin`): PASS. Witness = `Γ''` above (`p'' = p+2`, `ea, eb, own` of `anpKey2_fix`); all clauses asserted; last clause numerically `≤ 0.9797`.
- `anpKey4_of_reduce` (`AnpKey4OfReducePin`) and `anpDetGhCaseIII_holds` (`AnpKey4CaseIIIHoldsPin`): PASS. Constants `(C'', c''/2)`; the exponent identities and the product step are in table (i); the merged pin `AnpDetGhCaseIII` is true as stated (no primed successor needed).
- Inspection: (1) `deg_s = 2` is used only for "every solid edge at `α` is `m₁` or `m₂`", consumed in the `x`-independence; (2) `NoA2 π`, `𝐃_π`, `(eq:Psi)` are not used (the region is dropped using `ξ ≥ 0`); (3) the self-loop of T2242 note (d) does not arise: in `Γ'` the `x`-copy of `α` and `a'_{r_t}` are distinct vertices (143 of 520 `(datum,t)` configurations have `β_t = a_{j_t}` / `b_{j_t}`; `Γ''` is `IsNested` in all, conj. 1 included), so the fixed-graph route needs no special case.
- §29: (1) no time variable; (2) no `1 - ilambda²/L²` boundary; (3) no `L^d ≤ W^K`; (4) no `∀ᶠ n`; (5) uniform in `(a,b)`, `(C,c)` chosen before `L`; (6) no lower bound on a parameter; (7) `ψ`, `θ` abstract; §64 (4): no grid lift.

Overall: PASS for all six targets.

## (b) Script output, Tue Oct  6 06:28:11 UTC 2026
```
$ git log -1 --format="%h %s"   (worktree clean: git status --short | wc -l =        0)
a588214 T2260: LW-12d Graph/AnpKey4 (proves anpDetGhCaseIII_holds, case (III) of lem:Anp_key_gh)
$ git diff --stat main...t/T2260
 RBM3D/Graph/AnpKey4.lean | 878 +++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean   |   2 +
 2 files changed, 880 insertions(+)
$ lake build RBM3D.Graph.AnpKey4 2>&1 | tail -1
Build completed successfully (3349 jobs).
$ lake build 2>&1 | tail -1   (full library; root RBM3D.lean does not yet import AnpKey4, the hub adds it at merge)
Build completed successfully (4063 jobs).
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Graph/AnpKey4.lean | wc -l
0
$ #print axioms of the 27 public theorems of AnpKey4 (ax.lean), grouped by script
exit 0
23 declarations [propext, Classical.choice, Quot.sound]:
  anpDetGhCaseIII_holds, anpKey4_caseIII_ne, anpKey4_degS_eq, anpKey4_ep_congr, anpKey4_F2, anpKey4_factor, anpKey4_gh2_props, anpKey4_indep, anpKey4_inst_chain, anpKey4_inst_figAuxGh, anpKey4_inst_figLoop, anpKey4_inst_gh2, anpKey4_inst_hyp, anpKey4_inst_ne_solid, anpKey4_inst_reduce, anpKey4_lab_indep, anpKey4_of_reduce, anpKey4_pos_false, anpKey4_pos_true, anpKey4_reduce, anpKey4_seg, anpKey4_side, anpKey4_solid
4 declarations [propext, Quot.sound]:
  anpKey4_gh2_edges, anpKey4_head_shape, anpKey4_last_shape, anpKey4_ng_false
$ registry pre-check: lake build RBM3D.Test.Axioms; lake env lean pre.lean   (pre.lean = import RBM3D, import RBM3D.Graph.AnpKey4, #assert_rbm_axioms)
Build completed successfully (2 jobs).
exit 0
axiom audit: 7645 theorems, 2561 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
lines containing 'error': 0
$ pin check: check file T2260-check.lean section 2 in a scratch namespace, + 8 examples (pins.lean); lake env lean pins.lean
exit 0; lines containing 'error': 0
example : AnpKey4CaseIIIHoldsPin := @anpDetGhCaseIII_holds
example : AnpKey4NePin := @anpKey4_caseIII_ne
example : AnpKey4SolidPin := @anpKey4_solid
example : AnpKey4Gh2Pin := @anpKey4_gh2_props
example : AnpKey4ReducePin := @anpKey4_reduce
example : AnpKey4OfReducePin := @anpKey4_of_reduce
example : figLoop = anpKey4_figLoop := rfl
example : piLoop = anpKey4_piLoop := rfl
$ mathlib/core names used (mchk.lean: #check @n for 56 names)
exit 0; lines containing 'error': 0
$ name-clash grep of the 30 new public names (clash.sh)
new public names:       30
hits in RBM3D/ (this worktree, outside AnpKey4.lean): 3
hits in T2261 ticket, check file, worktree: 0
hits in main RBM3D/ and T2255 worktree: 0
prefix scan (anpKey4_*, anpDetGhCaseIII_holds, AnpKey4*) outside AnpKey4.lean in this worktree:
RBM3D/Test/Axioms.lean:310
RBM3D/Test/Axioms.lean:311
RBM3D/Graph/AnpKey2.lean:176
$ public declarations (script: grep of theorem/def at column 0)
57 anpKey4_ng_false 68 anpKey4_caseIII_ne 94 anpKey4_head_shape
121 anpKey4_last_shape 151 anpKey4_side 202 anpKey4_degS_eq
227 anpKey4_solid 277 anpKey4_gh2_props 342 anpKey4_gh2_edges
376 anpKey4_pos_false 400 anpKey4_pos_true 415 anpKey4_seg
476 anpKey4_lab_indep 489 anpKey4_factor 511 anpKey4_indep
525 anpKey4_ep_congr 538 anpKey4_F2 563 anpKey4_reduce
699 anpKey4_of_reduce 784 anpDetGhCaseIII_holds 795 anpKey4_figLoop
802 anpKey4_piLoop 805 anpKey4_eL 808 anpKey4_inst_hyp
821 anpKey4_inst_figLoop 828 anpKey4_inst_figAuxGh 835 anpKey4_inst_chain
840 anpKey4_inst_reduce 849 anpKey4_inst_ne_solid 864 anpKey4_inst_gh2
```

### Target and intermediate pins, extracted by script (python3 extract.py NAME; line:text)
```
784: theorem anpDetGhCaseIII_holds : ∀ d : ℕ, AnpDetGhCaseIII d :=
68: theorem anpKey4_caseIII_ne :
69:     ∀ (p q : ℕ) (Γ : NGraph p q) (π : Fin q → Fin p → Bool) (i : Fin q) (j₁ j₂ : Fin p) (s₁ s₂ : Bool)
70:       (k₁ k₂ : Fin Γ.es.length),
71:       Γ.GhostOK → Γ.IsNested → (j₁, s₁) ≠ (j₂, s₂) →
72:       Γ.IsB2 π j₁ s₁ k₁ i → Γ.IsB2 π j₂ s₂ k₂ i → j₁ ≠ j₂ := by
227: theorem anpKey4_solid :
228:     ∀ (p q : ℕ) (Γ : NGraph p q) (π : Fin q → Fin p → Bool) (i : Fin q) (j₁ j₂ : Fin p) (s₁ s₂ : Bool)
229:       (k₁ k₂ : Fin Γ.es.length),
230:       Γ.GhostOK → Γ.IsNested → j₁ ≠ j₂ → Γ.IsB2 π j₁ s₁ k₁ i → Γ.IsB2 π j₂ s₂ k₂ i → Γ.degS i = 2 →
231:       ∃ m₁ m₂ : Fin Γ.es.length, m₁ ≠ m₂ ∧
232:         (Γ.es.get m₁).ghost = false ∧ (Γ.es.get m₂).ghost = false ∧
233:         ((Γ.es.get m₁).u = Sum.inr i ∨ (Γ.es.get m₁).v = Sum.inr i) ∧
234:         ((Γ.es.get m₂).u = Sum.inr i ∨ (Γ.es.get m₂).v = Sum.inr i) ∧
235:         (s₁ = false → ∃ w rest, Γ.path j₁ = (k₁, Sum.inr i) :: (m₁, w) :: rest) ∧
236:         (s₁ = true → ∃ pre : List (Fin Γ.es.length × NV p q),
237:           Γ.path j₁ = pre ++ [(m₁, Sum.inr i), (k₁, Sum.inl (Sum.inr j₁))]) ∧
238:         (s₂ = false → ∃ w rest, Γ.path j₂ = (k₂, Sum.inr i) :: (m₂, w) :: rest) ∧
239:         (s₂ = true → ∃ pre : List (Fin Γ.es.length × NV p q),
240:           Γ.path j₂ = pre ++ [(m₂, Sum.inr i), (k₂, Sum.inl (Sum.inr j₂))]) ∧
241:         ∀ k : Fin Γ.es.length, (Γ.es.get k).ghost = false →
242:           ((Γ.es.get k).u = Sum.inr i ∨ (Γ.es.get k).v = Sum.inr i) → k = m₁ ∨ k = m₂ := by
277: theorem anpKey4_gh2_props :
278:     ∀ (p q : ℕ) (Γ : NGraph p q), Γ.GhostOK → Γ.IsNested → ∀ (r₁ r₂ : Fin p), r₁ ≠ r₂ →
279:       ∀ st₁ st₂ : Fin Γ.es.length × NV p q,
280:         st₁ ∈ Γ.path r₁ → ((Γ.path r₁).head? = some st₁ ∨ (Γ.path r₁).getLast? = some st₁) →
281:         st₂ ∈ Γ.path r₂ → ((Γ.path r₂).head? = some st₂ ∨ (Γ.path r₂).getLast? = some st₂) →
282:         Γ.noGhostPath r₁ = true → Γ.noGhostPath r₂ = true →
283:         (anpKey3_gh2 Γ st₁.1 st₂.1).GhostOK ∧ (anpKey3_gh2 Γ st₁.1 st₂.1).IsNested ∧
284:           (anpKey3_gh2 Γ st₁.1 st₂.1).nSolid + 2 = Γ.nSolid ∧
285:           (∀ r, (anpKey3_gh2 Γ st₁.1 st₂.1).noGhostPath r = true ↔
286:             Γ.noGhostPath r = true ∧ r ≠ r₁ ∧ r ≠ r₂) ∧
287:           (∀ (ι : Type) (ξ : ι → ι → ℝ) (lab : NV p q → ι),
288:             anpKey2_ep Γ ξ lab = ξ (lab (Γ.es.get st₁.1).u) (lab (Γ.es.get st₁.1).v) *
289:               ξ (lab (Γ.es.get st₂.1).u) (lab (Γ.es.get st₂.1).v) *
290:                 anpKey2_ep (anpKey3_gh2 Γ st₁.1 st₂.1) ξ lab) := by
563: theorem anpKey4_reduce :
564:     ∀ (p q : ℕ) (Γ : NGraph p (q + 1)) (π : Fin (q + 1) → Fin p → Bool),
565:       Γ.GhostOK → Γ.IsNested → AnpCaseIII Γ π →
566:       ∃ (p'' : ℕ) (Γ'' : NGraph p'' q) (ea eb : Fin p'' → Option (Fin p ⊕ Fin p)) (own : Fin p'' → Fin p),
567:         (Γ''.GhostOK ∧ Γ''.IsNested) ∧ Γ''.ordN = Γ.ordN ∧
568:         (∀ r, ea r = some (Sum.inl (own r)) ∨ ea r = none) ∧
569:         (∀ r, eb r = some (Sum.inr (own r)) ∨ eb r = none) ∧
570:         (∀ j, ∃! r, ea r = some (Sum.inl j)) ∧ (∀ j, ∃! r, eb r = some (Sum.inr j)) ∧
571:         (∀ r, Γ.noGhostPath (own r) = true → Γ''.noGhostPath r = true) ∧
572:         (∀ (d L : ℕ) [NeZero L] (ξ : Zd d L → Zd d L → ℝ) (θ : ℝ),
573:           (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) → (∀ α, ∑ β, ξ α β ^ 2 ≤ θ) →
574:           ∀ (a b : Fin p → Zd d L) (x₀ : Zd d L),
575:             Γ.valOn ξ a b (anpKey2_region a b π) ≤
576:               θ * Γ''.val ξ (fun r => anpKey2_fixLab a b x₀ (ea r)) (fun r => anpKey2_fixLab a b x₀ (eb r))) := by
699: theorem anpKey4_of_reduce
700:     (hred : ∀ (p q : ℕ) (Γ : NGraph p (q + 1)) (π : Fin (q + 1) → Fin p → Bool),
   ... [11 lines elided by the extraction script: hypothesis `hred`, the body of anpKey4_reduce] ...
712:               θ * Γ''.val ξ (fun r => anpKey2_fixLab a b x₀ (ea r)) (fun r => anpKey2_fixLab a b x₀ (eb r)))) :
713:     ∀ d : ℕ, AnpDetGhCaseIII d := by
```

### Compiled nonempty instances (statements extracted by script)
```
def anpKey4_figLoop : NGraph 2 1 where
  es := [⟨true, .inl (.inl 0), .inr 0⟩, ⟨false, .inr 0, .inl (.inl 0)⟩, ⟨false, .inl (.inl 0), .inl (.inr 0)⟩,
         ⟨true, .inl (.inl 1), .inr 0⟩, ⟨false, .inr 0, .inl (.inr 1)⟩]
  path := fun i => if i = 0 then [(0, .inr 0), (1, .inl (.inl 0)), (2, .inl (.inr 0))]
    else [(3, .inr 0), (4, .inl (.inr 1))]

802: def anpKey4_piLoop : Fin 1 → Fin 2 → Bool := fun _ _ => false
808: theorem anpKey4_inst_hyp :
809:     anpKey4_figLoop.GhostOK ∧ anpKey4_figLoop.IsNested ∧ anpKey4_figLoop.NoA2 anpKey4_piLoop ∧
810:       ¬ AnpCaseI anpKey4_figLoop anpKey4_piLoop ∧ AnpCaseIII anpKey4_figLoop anpKey4_piLoop ∧
811:       anpKey4_figLoop.ordN = 1 ∧ anpKey4_figLoop.nngh = 0 := by
821: theorem anpKey4_inst_figLoop :
822:     AnpIH 3 1 → AnpDetGhRegAt 3 anpKey4_figLoop anpKey4_piLoop := fun hIH =>
828: theorem anpKey4_inst_figAuxGh :
829:     AnpCaseIII anpKey2_figAuxGh (fun _ _ => false) ∧
830:       (AnpIH 3 2 → AnpDetGhRegAt 3 anpKey2_figAuxGh (fun _ _ => false)) := by
835: theorem anpKey4_inst_chain : AnpDetGhCaseIV 3 → LWAnpKeyGh 3 :=
840: theorem anpKey4_inst_reduce :
841:     ∃ (p'' : ℕ) (Γ'' : NGraph p'' 0), Γ''.GhostOK ∧ Γ''.IsNested ∧ Γ''.ordN = anpKey4_figLoop.ordN := by
849: theorem anpKey4_inst_ne_solid :
850:     (0 : Fin 2) ≠ 1 ∧ ∃ m₁ m₂ : Fin anpKey4_figLoop.es.length, m₁ ≠ m₂ ∧
851:       (anpKey4_figLoop.es.get m₁).ghost = false ∧ (anpKey4_figLoop.es.get m₂).ghost = false := by
864: theorem anpKey4_inst_gh2 :
865:     (anpKey3_gh2 figAux (anpKey2_eAux 0) (anpKey2_eAux 5)).GhostOK ∧
866:       (anpKey3_gh2 figAux (anpKey2_eAux 0) (anpKey2_eAux 5)).IsNested ∧
867:       (anpKey3_gh2 figAux (anpKey2_eAux 0) (anpKey2_eAux 5)).nSolid + 2 = figAux.nSolid := by
```

### Narrative (route as implemented; line numbers are those of the committed `RBM3D/Graph/AnpKey4.lean`)

1. `anpKey4_caseIII_ne` (:68): two B2 steps of one path are one step (`anpKey2_ghost_unique`, `GhostOK`), so `k₁ = k₂`; `anpKey2_endAt_ends` then makes this one edge join `α` to both `a_j` and `b_j`, a contradiction. This differs from the ticket's route (length `≥ 2` versus length `1`): no length split is needed.
2. `anpKey4_solid` (:227): `anpKey4_head_shape` (:94) and `anpKey4_last_shape` (:121) read the neighbouring step `(m, ·)` of the B2 step off `anpKey2_walkOK_iff` / `anpKey2_chain_snoc`; `m` is solid by `anpKey2_ghost_unique` and `Nodup` of the edge list (`anpKey4_side` :151); `m₁ ≠ m₂` is conjunct 4 of `IsNested`; the last clause is `deg_s = 2` through `anpKey4_degS_eq` (:202) and `Finset.card_eq_three` (:262-264).
3. `anpKey4_gh2_props` (:277): the proof of `anpKey3_gh2_props` with "one-step path" replaced by "first or last step" (head/last of the mapped path by `List.head?_map`, `List.getLast?_map`).
4. Positions (:376, :400, :415): the segment after the arrival `(k, α)` is `⟨j, 1⟩` (`anpKey2_seg_succ_pos`, `anpKey2_seg_head`); the segment ending with the arrival `(m, α)` comes from `anpKey2_cover` and `anpKey2_steps_arrival`. `r'_t ≠ r_t` because the head (last) step of `r_t` is `em k_t` (ghost) and that of `r'_t` is `em m_t` (solid); `r'_t` is ghost free by `anpKey2_fixV_noGhost2`. `r_t` comes from `anpKey2_fixV_end` and is not named explicitly.
5. Section 4 (:476-:538): `anpKey4_F2` is (F2) of `anpKey2_fix` for the explicit fixed graph; `anpKey4_factor` gives the factor `ξ(x, y_t(ℓ))` with `y_t` free of `x`; `anpKey4_gh2_edges` (:342), `anpKey4_ep_congr`, `anpKey4_indep` give `ep Γ'' ` independent of `x`: every solid edge of `Γ''` is `em k` with `k` solid, `k ∉ {m₁, m₂}`, hence not at `α` (last clause of `anpKey4_solid`, used at :656-659). This is the only use of `deg_s = 2`.
6. `anpKey4_reduce` (:563): witness `Γ'' = anpKey3_gh2 (anpKey2_fixV Γ i₀ s₀) (em m₁) (em m₂)`, `p'' = anpKey2_P Γ i₀`, `ea eb own` the `anpKey2_` ones. Value bound: (F3) `anpKey2_fixV_value` (:620), `choose` of the factors `y₁ ℓ`, `y₂ ℓ`, `Finset.sum_comm`, `anpKey3_sum_xx`, `anpKey2_ep_nonneg`.
7. `anpKey4_of_reduce` (:699) is the tail of `anpDetGhCaseI_holds` (`AnpKey3`) with the free label `x₀ := 0` (:725), `anpKey3_far_gen` (:739), `anpKey3_prod` (:751), the `ψ(0)` exponents by `zpow_add₀` (:759), constants `(C, c/2)`. The merged `NoA2` argument is the unused `_` at :714; the region geometry is not used (only `anpKey2_fixV_value`, which drops it).
8. The target (:784-785) is `anpKey4_of_reduce anpKey4_reduce`; the merged pin `AnpDetGhCaseIII` is proved unchanged (no primed successor, no change to a merged file).
9. Registry (`RBM3D/Test/Axioms.lean:310-311`, `structuralProps`): the first pre-check run, before these lines, failed with `axiom audit: 2 premise(s) that no theorem of this development proves ... [RBM.Graph.NGraph.IsB2, RBM.Graph.AnpCaseIII]`. I added exactly these two (the ticket expected `IsB2` only; `AnpCaseIII` is an explicit hypothesis of `anpKey4_reduce` and `anpKey4_of_reduce`). The run above exits 0. No deletion: the owed line `AnpDetGhCaseIII` (`Test/Axioms.lean:167`) stays until LW-12f.
10. Instances (:795-:864): (1) at `anpKey4_figLoop` (= check-file `figLoop`, the `β_0 = a_0` self-loop configuration; case (III) only) every deterministic hypothesis, `ordN = 1`, `nngh = 0` by `decide +kernel`; (2), (3) the target applied at `anpKey4_figLoop` and `anpKey2_figAuxGh` (`ℳ₂`); (4) the chain to `LWAnpKeyGh 3`; (5) `anpKey4_reduce` at `anpKey4_figLoop`; (6) `anpKey4_caseIII_ne`, `anpKey4_solid` there; (7) `anpKey4_gh2_props` at `figAux` with the first step of path 0 and the last step of the three-step path 1. The only premise of (2), (3) is `AnpIH 3 k` (registered owed, `Test/Axioms.lean:169`; discharged by `anpDetGh_of_step` in LW-12f).
11. No section (a′): nothing in (a) conflicted with the proof. The numerics of (a) were run by the preflight stage; I did not rerun them.

## (c) Mathlib/core names used (script: grep of the file, then `#check @n` for each, `mchk.lean`: exit 0, no error)
Bool.and_eq_true, Bool.false_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff, Bool.or_eq_true, Fin.exists_succAbove_eq, Fin.insertNth_apply_same,
Fin.insertNth_apply_succAbove, Finset.card_eq_three, Finset.card_filter, Finset.card_le_card, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
Finset.mem_univ, Finset.mul_sum, Finset.prod_nonneg, Finset.sum_comm, Finset.sum_congr, Finset.sum_le_sum, Finset.sum_mul,
List.concat_eq_append, List.countP_cons_of_pos, List.eq_nil_or_concat, List.filter_cons_of_neg, List.filter_cons_of_pos, List.get_eq_getElem, List.get_mem,
List.getLast?_eq_some_iff, List.getLast?_map, List.head?_map, List.length_cons, List.map_append, List.map_congr_left, List.map_cons,
List.mem_cons, List.mem_iff_get, List.mem_map, List.mem_of_getLast?, List.mem_of_mem_head?, List.nodup_append, List.nodup_cons,
List.ofFn_getElem_eq_map, List.sum_cons, List.sum_ofFn, mul_le_mul_of_nonneg_left, mul_le_mul_of_nonneg_right, Nat.cast_nonneg, Nat.lt_succ_self,
pow_pos, Set.mem_Ici, Sum.elim_inr, zpow_add₀, zpow_pos, Fin.insertNth, Sum.elim.
Names verified absent: none looked up (no name was invented; every one above was checked by `#check`).

## (d) Open issues and paper-delta candidates
- Registry: `RBM.Graph.NGraph.IsB2` and `RBM.Graph.AnpCaseIII` added to `structuralProps` (`Test/Axioms.lean:310-311`), see narrative 9; nothing owed or borrowed added.
- Stale docstring (doc fix for the dispatcher, no statement difference): `AnpKey2.lean:176` cites `7_8:1376-1384` for case (III); the case is `7_8:1245-1348`. Merged file not edited.
- T2260a: no new ghost edges `(a_t, β_t)` (`7_8:1252-1254`): after vertex fixing the B2 edges stay one-step ghost paths and the solid edges `(α_q, β_t)` become ghost ending edges of their segments (`anpKey3_gh2` on `anpKey2_fixV`); the paper's `𝒢^new` has a ghost self-loop when `β_t = a_t`, which property (1) of `lem:Anp_key` forbids; this route has no such case (`anpKey4_inst_reduce`, `anpKey4_inst_figLoop`).
- T2260b: both sides allowed, no WLOG `(a_1, α_q)`, `(a_2, α_q)`: B2 at `a_{j_t}` or `b_{j_t}` (the side bit `s_t` in `anpKey4_solid`).
- T2260c: "these B2 edges do not belong to the same path" (`7_8:1246`) follows from `GhostOK` and the walk property (`anpKey4_caseIII_ne`).
- T2260d: the region `𝐃_π`, `(eq:noA2)` and `(eq:Psi)` are not used (`(kwuyayw_case3)` holds for the sum over all labels, the region is dropped by `ξ ≥ 0` in (F3)); `deg_s = 2` is used only to make `x` occur on the ghost edges `m₁`, `m₂` only.
- T2260e: `ord(𝒢'') = ord(𝒢)` exactly (`Γ''.ordN = Γ.ordN` in `anpKey4_reduce`); the ghost-free surplus `n_ngh(𝒢'') ≥ n_ngh(𝒢)` is absorbed by `anpKey3_prod` (`ψ(c|·|) ≤ ψ(0)`), `c ↦ c/2` as in the paper's `:1347`.
